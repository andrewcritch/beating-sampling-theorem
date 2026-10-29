import BstLean.Part266Shard6Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12500. -/
namespace BstLean.Part266.Row12500
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12498 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12498 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12498 128 ≤ (12752 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12752 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12500) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12500 : ℕ))
    (by norm_num : (12500 : ℕ) ≤ 16384)
  have ht : paperTail256 12500 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12500 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12500 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12500 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12500 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12500 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12498 128 * √(2 / (12500 : ℝ)) *
      (√(12500 : ℝ) + paperT0 12500 + paperTail256 12500) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12500 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12500 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12500 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12498 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12498 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12500 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12500

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12500
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12500 (61 / 100) 161 (17 / (100 * 12500)) (26 / (10 * 12500)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12500 (61 / 100) 161 (17 / (100 * 12500)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (499791967 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1599334319 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (726514161 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12500 / 12500 * (61 / 100)) ^ 4 * inverseRadius8 (12500 - 1) /
            envelopeGap 12500 (61 / 100) 161 (17 / (100 * 12500)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12500

namespace BstLean.Part266.Row12500
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12500 161 ≤ (298014321 / 62500000000000000)
  f1 : (tableEnvelope C).f1 12500 161 ≤ (198845237 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (382340167 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12500 161 ≤ (1922613427 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12500 161 ≤ (341975667 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12500 161 ≤ (249898799 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (499791967 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (499791967 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1599334319 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (726514161 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3687817 / 1000000000) : ℝ) ≤ √(17 / (100 * 12500) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12500) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1117801377 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19995839061 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12500) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12500) ≤ (22627417 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12500) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12500 * (161 : ℝ) ^ 2 + 26 / (10 * 12500) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12500) : ℝ)) (tA 12500 * 161 ^ 2 + 26 / (10 * 12500)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3687817 / 1000000000))) * ((499791967 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3687817 / 1000000000)) ^ 3) * ((1599334319 / 1000000000000000000000000))) + ((726514161 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3687817 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12500) : ℝ)) d.D d.V d.P (√(tA 12500) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3687817 / 1000000000)) ^ 2 * (((1117801377 / 500000000000000)) * ((19995839061 / 500000000000000000)))) + ((726514161 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12500) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3687817 / 1000000000)) * ((499791967 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12500) : ℝ)) (tA 12500 * 161 ^ 2 + 26 / (10 * 12500)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((499791967 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3687817 / 1000000000)) ^ 2) * ((1599334319 / 1000000000000000000000000)) + ((726514161 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12500) : ℝ)) (√(26 / (10 * 12500) : ℝ)) d.D d.V d.P (√(tA 12500) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3687817 / 1000000000)) * (((1117801377 / 500000000000000)) * ((19995839061 / 500000000000000000))) + ((726514161 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12500) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((499791967 / 100000000000000000000) : ℝ) + ((726514161 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12500

namespace BstLean.Part266.Row12500
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12500 161 ∧
    0 ≤ (tableEnvelope C).f1 12500 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12500 161 ∧
    0 ≤ (tableEnvelope C).w1 12500 161 ∧ 0 ≤ (tableEnvelope C).w2 12500 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12500 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12500 161 ∧ 0 ≤ d.f1 12500 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12500 161 ∧ 0 ≤ d.w1 12500 161 ∧ 0 ≤ d.w2 12500 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12500 ≤ 2 * (228 / 100 : ℝ) / 12500 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12500 ≤ 2 * (370 / 100 : ℝ) / 12500 := by
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
    (completeRAData (tableEnvelope C) 12500 161).locationBound 12500 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12500 161).energyBound 12500 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12500 161) (d.f1 12500 161) d.f2 ≤
      32 * (((298014321 / 62500000000000000) : ℝ) + (198845237 / 125000000000000000) + (382340167 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12500 161) (d.w1 12500 161)
      (d.w2 12500 161) ≤
      32 * (((1922613427 / 100000000000000000000) : ℝ) + (341975667 / 25000000000000000000) + (249898799 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12500 161) (d.f1 12500 161) d.f2 ≤
      ((298014321 / 62500000000000000) : ℝ) ^ 2 + 2 * ((298014321 / 62500000000000000)) * ((198845237 / 125000000000000000)) * (126 / 100) +
      2 * (((198845237 / 125000000000000000)) ^ 2 + 2 * ((298014321 / 62500000000000000)) * ((382340167 / 1000000000000000000))) +
      6 * ((198845237 / 125000000000000000)) * ((382340167 / 1000000000000000000)) * (126 / 100) + 8 * ((382340167 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12500 161) (d.f1 12500 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12500 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12500 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12500 161) (d.f1 12500 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12500 161) (d.w1 12500 161) (d.w2 12500 161)
  have hwexpr0 : 0 ≤ d.w0 12500 161 + d.w1 12500 161 * √(π / 2) +
      2 * d.w2 12500 161 + energyR16 12500 *
      radiusPolynomialRoot16 (d.w0 12500 161) (d.w1 12500 161) (d.w2 12500 161) := by
    positivity
  constructor
  · change (12500 : ℝ) ^ 8 * (mA 12500 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12500 161) (d.f1 12500 161) d.f2 + locationR16 12500 *
        radiusPolynomialRoot16 (d.f0 12500 161) (d.f1 12500 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12500 : ℝ) ^ 8 * (mA 12500 : ℝ) ^ 8 *
        ((((298014321 / 62500000000000000) : ℝ) ^ 2 + 2 * ((298014321 / 62500000000000000)) * ((198845237 / 125000000000000000)) * (126 / 100) +
          2 * (((198845237 / 125000000000000000)) ^ 2 + 2 * ((298014321 / 62500000000000000)) * ((382340167 / 1000000000000000000))) +
          6 * ((198845237 / 125000000000000000)) * ((382340167 / 1000000000000000000)) * (126 / 100) + 8 * ((382340167 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12500) *
          (32 * (((298014321 / 62500000000000000) : ℝ) + (198845237 / 125000000000000000) + (382340167 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12500 : ℝ) ^ 16 *
      (d.w0 12500 161 + d.w1 12500 161 * √(π / 2) + 2 * d.w2 12500 161 +
        energyR16 12500 * radiusPolynomialRoot16 (d.w0 12500 161) (d.w1 12500 161)
          (d.w2 12500 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12500 : ℝ) ^ 16 *
        (((1922613427 / 100000000000000000000) : ℝ) + ((341975667 / 25000000000000000000)) * (126 / 100) + 2 * ((249898799 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12500) *
          (32 * (((1922613427 / 100000000000000000000) : ℝ) + (341975667 / 25000000000000000000) + (249898799 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12500

/-! A coarse bound on the actual paper statistics constant at dimension 12501. -/
namespace BstLean.Part266.Row12501
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12499 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12499 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12499 128 ≤ (12753 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12753 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12501) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12501 : ℕ))
    (by norm_num : (12501 : ℕ) ≤ 16384)
  have ht : paperTail256 12501 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12501 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12501 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12501 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12501 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12501 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12499 128 * √(2 / (12501 : ℝ)) *
      (√(12501 : ℝ) + paperT0 12501 + paperTail256 12501) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12501 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12501 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12501 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12499 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12499 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12501 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12501

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12501
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12501 (61 / 100) 161 (17 / (100 * 12501)) (26 / (10 * 12501)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12501 (61 / 100) 161 (17 / (100 * 12501)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (49967203 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (799411307 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5808358403 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12501 / 12501 * (61 / 100)) ^ 4 * inverseRadius8 (12501 - 1) /
            envelopeGap 12501 (61 / 100) 161 (17 / (100 * 12501)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12501

namespace BstLean.Part266.Row12501
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12501 161 ≤ (4767273683 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12501 161 ≤ (1590443333 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (382263653 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12501 161 ≤ (96107583 / 5000000000000000000)
  w1 : (tableEnvelope C).w1 12501 161 ≤ (1367574219 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12501 161 ≤ (499677657 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (49967203 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (49967203 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (799411307 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5808358403 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((368767 / 100000000) : ℝ) ≤ √(17 / (100 * 12501) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12501) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1117667247 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39985279967 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12501) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12501) ≤ (22625607 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12501) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12501 * (161 : ℝ) ^ 2 + 26 / (10 * 12501) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12501) : ℝ)) (tA 12501 * 161 ^ 2 + 26 / (10 * 12501)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((368767 / 100000000))) * ((49967203 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((368767 / 100000000)) ^ 3) * ((799411307 / 500000000000000000000000))) + ((5808358403 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((368767 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12501) : ℝ)) d.D d.V d.P (√(tA 12501) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((368767 / 100000000)) ^ 2 * (((1117667247 / 500000000000000)) * ((39985279967 / 1000000000000000000)))) + ((5808358403 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12501) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((368767 / 100000000)) * ((49967203 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12501) : ℝ)) (tA 12501 * 161 ^ 2 + 26 / (10 * 12501)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((49967203 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((368767 / 100000000)) ^ 2) * ((799411307 / 500000000000000000000000)) + ((5808358403 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12501) : ℝ)) (√(26 / (10 * 12501) : ℝ)) d.D d.V d.P (√(tA 12501) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((368767 / 100000000)) * (((1117667247 / 500000000000000)) * ((39985279967 / 1000000000000000000))) + ((5808358403 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12501) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((49967203 / 10000000000000000000) : ℝ) + ((5808358403 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12501

namespace BstLean.Part266.Row12501
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12501 161 ∧
    0 ≤ (tableEnvelope C).f1 12501 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12501 161 ∧
    0 ≤ (tableEnvelope C).w1 12501 161 ∧ 0 ≤ (tableEnvelope C).w2 12501 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12501 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12501 161 ∧ 0 ≤ d.f1 12501 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12501 161 ∧ 0 ≤ d.w1 12501 161 ∧ 0 ≤ d.w2 12501 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12501 ≤ 2 * (228 / 100 : ℝ) / 12501 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12501 ≤ 2 * (370 / 100 : ℝ) / 12501 := by
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
    (completeRAData (tableEnvelope C) 12501 161).locationBound 12501 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12501 161).energyBound 12501 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12501 161) (d.f1 12501 161) d.f2 ≤
      32 * (((4767273683 / 1000000000000000000) : ℝ) + (1590443333 / 1000000000000000000) + (382263653 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12501 161) (d.w1 12501 161)
      (d.w2 12501 161) ≤
      32 * (((96107583 / 5000000000000000000) : ℝ) + (1367574219 / 100000000000000000000) + (499677657 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12501 161) (d.f1 12501 161) d.f2 ≤
      ((4767273683 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4767273683 / 1000000000000000000)) * ((1590443333 / 1000000000000000000)) * (126 / 100) +
      2 * (((1590443333 / 1000000000000000000)) ^ 2 + 2 * ((4767273683 / 1000000000000000000)) * ((382263653 / 1000000000000000000))) +
      6 * ((1590443333 / 1000000000000000000)) * ((382263653 / 1000000000000000000)) * (126 / 100) + 8 * ((382263653 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12501 161) (d.f1 12501 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12501 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12501 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12501 161) (d.f1 12501 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12501 161) (d.w1 12501 161) (d.w2 12501 161)
  have hwexpr0 : 0 ≤ d.w0 12501 161 + d.w1 12501 161 * √(π / 2) +
      2 * d.w2 12501 161 + energyR16 12501 *
      radiusPolynomialRoot16 (d.w0 12501 161) (d.w1 12501 161) (d.w2 12501 161) := by
    positivity
  constructor
  · change (12501 : ℝ) ^ 8 * (mA 12501 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12501 161) (d.f1 12501 161) d.f2 + locationR16 12501 *
        radiusPolynomialRoot16 (d.f0 12501 161) (d.f1 12501 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12501 : ℝ) ^ 8 * (mA 12501 : ℝ) ^ 8 *
        ((((4767273683 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4767273683 / 1000000000000000000)) * ((1590443333 / 1000000000000000000)) * (126 / 100) +
          2 * (((1590443333 / 1000000000000000000)) ^ 2 + 2 * ((4767273683 / 1000000000000000000)) * ((382263653 / 1000000000000000000))) +
          6 * ((1590443333 / 1000000000000000000)) * ((382263653 / 1000000000000000000)) * (126 / 100) + 8 * ((382263653 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12501) *
          (32 * (((4767273683 / 1000000000000000000) : ℝ) + (1590443333 / 1000000000000000000) + (382263653 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12501 : ℝ) ^ 16 *
      (d.w0 12501 161 + d.w1 12501 161 * √(π / 2) + 2 * d.w2 12501 161 +
        energyR16 12501 * radiusPolynomialRoot16 (d.w0 12501 161) (d.w1 12501 161)
          (d.w2 12501 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12501 : ℝ) ^ 16 *
        (((96107583 / 5000000000000000000) : ℝ) + ((1367574219 / 100000000000000000000)) * (126 / 100) + 2 * ((499677657 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12501) *
          (32 * (((96107583 / 5000000000000000000) : ℝ) + (1367574219 / 100000000000000000000) + (499677657 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12501

/-! A coarse bound on the actual paper statistics constant at dimension 12502. -/
namespace BstLean.Part266.Row12502
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12500 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12500 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12500 128 ≤ (12754 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12754 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12502) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12502 : ℕ))
    (by norm_num : (12502 : ℕ) ≤ 16384)
  have ht : paperTail256 12502 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12502 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12502 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12502 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12502 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12502 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12500 128 * √(2 / (12502 : ℝ)) *
      (√(12502 : ℝ) + paperT0 12502 + paperTail256 12502) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12502 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12502 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12502 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12500 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12500 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12502 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12502

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12502
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12502 (61 / 100) 161 (17 / (100 * 12502)) (26 / (10 * 12502)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12502 (61 / 100) 161 (17 / (100 * 12502)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (499552131 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1598311113 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5804606249 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12502 / 12502 * (61 / 100)) ^ 4 * inverseRadius8 (12502 - 1) /
            envelopeGap 12502 (61 / 100) 161 (17 / (100 * 12502)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12502

namespace BstLean.Part266.Row12502
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12502 161 ≤ (1191580573 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12502 161 ≤ (1590125737 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (76437453 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12502 161 ≤ (76867633 / 4000000000000000000)
  w1 : (tableEnvelope C).w1 12502 161 ≤ (1367246253 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12502 161 ≤ (249778877 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (499552131 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (499552131 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1598311113 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5804606249 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1843761 / 500000000) : ℝ) ≤ √(17 / (100 * 12502) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12502) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (139691643 / 62500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39978883339 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12502) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12502) ≤ (56559493 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12502) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12502 * (161 : ℝ) ^ 2 + 26 / (10 * 12502) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12502) : ℝ)) (tA 12502 * 161 ^ 2 + 26 / (10 * 12502)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1843761 / 500000000))) * ((499552131 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1843761 / 500000000)) ^ 3) * ((1598311113 / 1000000000000000000000000))) + ((5804606249 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1843761 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12502) : ℝ)) d.D d.V d.P (√(tA 12502) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1843761 / 500000000)) ^ 2 * (((139691643 / 62500000000000)) * ((39978883339 / 1000000000000000000)))) + ((5804606249 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12502) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1843761 / 500000000)) * ((499552131 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12502) : ℝ)) (tA 12502 * 161 ^ 2 + 26 / (10 * 12502)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((499552131 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1843761 / 500000000)) ^ 2) * ((1598311113 / 1000000000000000000000000)) + ((5804606249 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12502) : ℝ)) (√(26 / (10 * 12502) : ℝ)) d.D d.V d.P (√(tA 12502) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1843761 / 500000000)) * (((139691643 / 62500000000000)) * ((39978883339 / 1000000000000000000))) + ((5804606249 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12502) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((499552131 / 100000000000000000000) : ℝ) + ((5804606249 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12502

namespace BstLean.Part266.Row12502
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12502 161 ∧
    0 ≤ (tableEnvelope C).f1 12502 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12502 161 ∧
    0 ≤ (tableEnvelope C).w1 12502 161 ∧ 0 ≤ (tableEnvelope C).w2 12502 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12502 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12502 161 ∧ 0 ≤ d.f1 12502 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12502 161 ∧ 0 ≤ d.w1 12502 161 ∧ 0 ≤ d.w2 12502 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12502 ≤ 2 * (228 / 100 : ℝ) / 12502 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12502 ≤ 2 * (370 / 100 : ℝ) / 12502 := by
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
    (completeRAData (tableEnvelope C) 12502 161).locationBound 12502 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12502 161).energyBound 12502 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12502 161) (d.f1 12502 161) d.f2 ≤
      32 * (((1191580573 / 250000000000000000) : ℝ) + (1590125737 / 1000000000000000000) + (76437453 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12502 161) (d.w1 12502 161)
      (d.w2 12502 161) ≤
      32 * (((76867633 / 4000000000000000000) : ℝ) + (1367246253 / 100000000000000000000) + (249778877 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12502 161) (d.f1 12502 161) d.f2 ≤
      ((1191580573 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1191580573 / 250000000000000000)) * ((1590125737 / 1000000000000000000)) * (126 / 100) +
      2 * (((1590125737 / 1000000000000000000)) ^ 2 + 2 * ((1191580573 / 250000000000000000)) * ((76437453 / 200000000000000000))) +
      6 * ((1590125737 / 1000000000000000000)) * ((76437453 / 200000000000000000)) * (126 / 100) + 8 * ((76437453 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12502 161) (d.f1 12502 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12502 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12502 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12502 161) (d.f1 12502 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12502 161) (d.w1 12502 161) (d.w2 12502 161)
  have hwexpr0 : 0 ≤ d.w0 12502 161 + d.w1 12502 161 * √(π / 2) +
      2 * d.w2 12502 161 + energyR16 12502 *
      radiusPolynomialRoot16 (d.w0 12502 161) (d.w1 12502 161) (d.w2 12502 161) := by
    positivity
  constructor
  · change (12502 : ℝ) ^ 8 * (mA 12502 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12502 161) (d.f1 12502 161) d.f2 + locationR16 12502 *
        radiusPolynomialRoot16 (d.f0 12502 161) (d.f1 12502 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12502 : ℝ) ^ 8 * (mA 12502 : ℝ) ^ 8 *
        ((((1191580573 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1191580573 / 250000000000000000)) * ((1590125737 / 1000000000000000000)) * (126 / 100) +
          2 * (((1590125737 / 1000000000000000000)) ^ 2 + 2 * ((1191580573 / 250000000000000000)) * ((76437453 / 200000000000000000))) +
          6 * ((1590125737 / 1000000000000000000)) * ((76437453 / 200000000000000000)) * (126 / 100) + 8 * ((76437453 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12502) *
          (32 * (((1191580573 / 250000000000000000) : ℝ) + (1590125737 / 1000000000000000000) + (76437453 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12502 : ℝ) ^ 16 *
      (d.w0 12502 161 + d.w1 12502 161 * √(π / 2) + 2 * d.w2 12502 161 +
        energyR16 12502 * radiusPolynomialRoot16 (d.w0 12502 161) (d.w1 12502 161)
          (d.w2 12502 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12502 : ℝ) ^ 16 *
        (((76867633 / 4000000000000000000) : ℝ) + ((1367246253 / 100000000000000000000)) * (126 / 100) + 2 * ((249778877 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12502) *
          (32 * (((76867633 / 4000000000000000000) : ℝ) + (1367246253 / 100000000000000000000) + (249778877 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12502

/-! A coarse bound on the actual paper statistics constant at dimension 12503. -/
namespace BstLean.Part266.Row12503
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12501 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12501 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12501 128 ≤ (12755 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12755 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12503) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12503 : ℕ))
    (by norm_num : (12503 : ℕ) ≤ 16384)
  have ht : paperTail256 12503 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12503 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12503 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12503 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12503 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12503 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12501 128 * √(2 / (12503 : ℝ)) *
      (√(12503 : ℝ) + paperT0 12503 + paperTail256 12503) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12503 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12503 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12503 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12501 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12501 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12503 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12503

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12503
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12503 (61 / 100) 161 (17 / (100 * 12503)) (26 / (10 * 12503)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12503 (61 / 100) 161 (17 / (100 * 12503)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (49943227 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1597799817 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (232034273 / 40000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12503 / 12503 * (61 / 100)) ^ 4 * inverseRadius8 (12503 - 1) /
            envelopeGap 12503 (61 / 100) 161 (17 / (100 * 12503)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12503

namespace BstLean.Part266.Row12503
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12503 161 ≤ (297835469 / 62500000000000000)
  f1 : (tableEnvelope C).f1 12503 161 ≤ (794903691 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (382110797 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12503 161 ≤ (96061469 / 5000000000000000000)
  w1 : (tableEnvelope C).w1 12503 161 ≤ (1366918027 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12503 161 ≤ (49943789 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (49943227 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (49943227 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1597799817 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (232034273 / 40000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((29499 / 8000000) : ℝ) ≤ √(17 / (100 * 12503) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12503) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (446959627 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9993122063 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12503) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12503) ≤ (113109939 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12503) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12503 * (161 : ℝ) ^ 2 + 26 / (10 * 12503) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12503) : ℝ)) (tA 12503 * 161 ^ 2 + 26 / (10 * 12503)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((29499 / 8000000))) * ((49943227 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((29499 / 8000000)) ^ 3) * ((1597799817 / 1000000000000000000000000))) + ((232034273 / 40000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((29499 / 8000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12503) : ℝ)) d.D d.V d.P (√(tA 12503) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((29499 / 8000000)) ^ 2 * (((446959627 / 200000000000000)) * ((9993122063 / 250000000000000000)))) + ((232034273 / 40000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12503) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((29499 / 8000000)) * ((49943227 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12503) : ℝ)) (tA 12503 * 161 ^ 2 + 26 / (10 * 12503)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((49943227 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((29499 / 8000000)) ^ 2) * ((1597799817 / 1000000000000000000000000)) + ((232034273 / 40000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12503) : ℝ)) (√(26 / (10 * 12503) : ℝ)) d.D d.V d.P (√(tA 12503) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((29499 / 8000000)) * (((446959627 / 200000000000000)) * ((9993122063 / 250000000000000000))) + ((232034273 / 40000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12503) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((49943227 / 10000000000000000000) : ℝ) + ((232034273 / 40000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12503

namespace BstLean.Part266.Row12503
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12503 161 ∧
    0 ≤ (tableEnvelope C).f1 12503 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12503 161 ∧
    0 ≤ (tableEnvelope C).w1 12503 161 ∧ 0 ≤ (tableEnvelope C).w2 12503 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12503 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12503 161 ∧ 0 ≤ d.f1 12503 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12503 161 ∧ 0 ≤ d.w1 12503 161 ∧ 0 ≤ d.w2 12503 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12503 ≤ 2 * (228 / 100 : ℝ) / 12503 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12503 ≤ 2 * (370 / 100 : ℝ) / 12503 := by
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
    (completeRAData (tableEnvelope C) 12503 161).locationBound 12503 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12503 161).energyBound 12503 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12503 161) (d.f1 12503 161) d.f2 ≤
      32 * (((297835469 / 62500000000000000) : ℝ) + (794903691 / 500000000000000000) + (382110797 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12503 161) (d.w1 12503 161)
      (d.w2 12503 161) ≤
      32 * (((96061469 / 5000000000000000000) : ℝ) + (1366918027 / 100000000000000000000) + (49943789 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12503 161) (d.f1 12503 161) d.f2 ≤
      ((297835469 / 62500000000000000) : ℝ) ^ 2 + 2 * ((297835469 / 62500000000000000)) * ((794903691 / 500000000000000000)) * (126 / 100) +
      2 * (((794903691 / 500000000000000000)) ^ 2 + 2 * ((297835469 / 62500000000000000)) * ((382110797 / 1000000000000000000))) +
      6 * ((794903691 / 500000000000000000)) * ((382110797 / 1000000000000000000)) * (126 / 100) + 8 * ((382110797 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12503 161) (d.f1 12503 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12503 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12503 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12503 161) (d.f1 12503 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12503 161) (d.w1 12503 161) (d.w2 12503 161)
  have hwexpr0 : 0 ≤ d.w0 12503 161 + d.w1 12503 161 * √(π / 2) +
      2 * d.w2 12503 161 + energyR16 12503 *
      radiusPolynomialRoot16 (d.w0 12503 161) (d.w1 12503 161) (d.w2 12503 161) := by
    positivity
  constructor
  · change (12503 : ℝ) ^ 8 * (mA 12503 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12503 161) (d.f1 12503 161) d.f2 + locationR16 12503 *
        radiusPolynomialRoot16 (d.f0 12503 161) (d.f1 12503 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12503 : ℝ) ^ 8 * (mA 12503 : ℝ) ^ 8 *
        ((((297835469 / 62500000000000000) : ℝ) ^ 2 + 2 * ((297835469 / 62500000000000000)) * ((794903691 / 500000000000000000)) * (126 / 100) +
          2 * (((794903691 / 500000000000000000)) ^ 2 + 2 * ((297835469 / 62500000000000000)) * ((382110797 / 1000000000000000000))) +
          6 * ((794903691 / 500000000000000000)) * ((382110797 / 1000000000000000000)) * (126 / 100) + 8 * ((382110797 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12503) *
          (32 * (((297835469 / 62500000000000000) : ℝ) + (794903691 / 500000000000000000) + (382110797 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12503 : ℝ) ^ 16 *
      (d.w0 12503 161 + d.w1 12503 161 * √(π / 2) + 2 * d.w2 12503 161 +
        energyR16 12503 * radiusPolynomialRoot16 (d.w0 12503 161) (d.w1 12503 161)
          (d.w2 12503 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12503 : ℝ) ^ 16 *
        (((96061469 / 5000000000000000000) : ℝ) + ((1366918027 / 100000000000000000000)) * (126 / 100) + 2 * ((49943789 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12503) *
          (32 * (((96061469 / 5000000000000000000) : ℝ) + (1366918027 / 100000000000000000000) + (49943789 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12503

/-! A coarse bound on the actual paper statistics constant at dimension 12504. -/
namespace BstLean.Part266.Row12504
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12502 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12502 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12502 128 ≤ (12756 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12756 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12504) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12504 : ℕ))
    (by norm_num : (12504 : ℕ) ≤ 16384)
  have ht : paperTail256 12504 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12504 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12504 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12504 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12504 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12504 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12502 128 * √(2 / (12504 : ℝ)) *
      (√(12504 : ℝ) + paperT0 12504 + paperTail256 12504) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12504 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12504 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12504 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12502 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12502 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12504 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12504

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12504
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12504 (61 / 100) 161 (17 / (100 * 12504)) (26 / (10 * 12504)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12504 (61 / 100) 161 (17 / (100 * 12504)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (7801757 / 1562500000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (798644363 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (362319383 / 62500000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12504 / 12504 * (61 / 100)) ^ 4 * inverseRadius8 (12504 - 1) /
            envelopeGap 12504 (61 / 100) 161 (17 / (100 * 12504)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12504

namespace BstLean.Part266.Row12504
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12504 161 ≤ (2382208391 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12504 161 ≤ (317897999 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (47754307 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12504 161 ≤ (480192217 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12504 161 ≤ (341647571 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12504 161 ≤ (31207379 / 6250000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (7801757 / 1562500000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (7801757 / 1562500000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (798644363 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (362319383 / 62500000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3687227 / 1000000000) : ℝ) ≤ √(17 / (100 * 12504) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12504) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (558632509 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19983047353 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12504) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12504) ≤ (113100893 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12504) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12504 * (161 : ℝ) ^ 2 + 26 / (10 * 12504) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12504) : ℝ)) (tA 12504 * 161 ^ 2 + 26 / (10 * 12504)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3687227 / 1000000000))) * ((7801757 / 1562500000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3687227 / 1000000000)) ^ 3) * ((798644363 / 500000000000000000000000))) + ((362319383 / 62500000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3687227 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12504) : ℝ)) d.D d.V d.P (√(tA 12504) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3687227 / 1000000000)) ^ 2 * (((558632509 / 250000000000000)) * ((19983047353 / 500000000000000000)))) + ((362319383 / 62500000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12504) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3687227 / 1000000000)) * ((7801757 / 1562500000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12504) : ℝ)) (tA 12504 * 161 ^ 2 + 26 / (10 * 12504)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((7801757 / 1562500000000000000) : ℝ) + (24198 / 100000) / (2 * ((3687227 / 1000000000)) ^ 2) * ((798644363 / 500000000000000000000000)) + ((362319383 / 62500000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12504) : ℝ)) (√(26 / (10 * 12504) : ℝ)) d.D d.V d.P (√(tA 12504) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3687227 / 1000000000)) * (((558632509 / 250000000000000)) * ((19983047353 / 500000000000000000))) + ((362319383 / 62500000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12504) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((7801757 / 1562500000000000000) : ℝ) + ((362319383 / 62500000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12504

namespace BstLean.Part266.Row12504
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12504 161 ∧
    0 ≤ (tableEnvelope C).f1 12504 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12504 161 ∧
    0 ≤ (tableEnvelope C).w1 12504 161 ∧ 0 ≤ (tableEnvelope C).w2 12504 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12504 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12504 161 ∧ 0 ≤ d.f1 12504 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12504 161 ∧ 0 ≤ d.w1 12504 161 ∧ 0 ≤ d.w2 12504 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12504 ≤ 2 * (228 / 100 : ℝ) / 12504 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12504 ≤ 2 * (370 / 100 : ℝ) / 12504 := by
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
    (completeRAData (tableEnvelope C) 12504 161).locationBound 12504 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12504 161).energyBound 12504 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12504 161) (d.f1 12504 161) d.f2 ≤
      32 * (((2382208391 / 500000000000000000) : ℝ) + (317897999 / 200000000000000000) + (47754307 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12504 161) (d.w1 12504 161)
      (d.w2 12504 161) ≤
      32 * (((480192217 / 25000000000000000000) : ℝ) + (341647571 / 25000000000000000000) + (31207379 / 6250000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12504 161) (d.f1 12504 161) d.f2 ≤
      ((2382208391 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2382208391 / 500000000000000000)) * ((317897999 / 200000000000000000)) * (126 / 100) +
      2 * (((317897999 / 200000000000000000)) ^ 2 + 2 * ((2382208391 / 500000000000000000)) * ((47754307 / 125000000000000000))) +
      6 * ((317897999 / 200000000000000000)) * ((47754307 / 125000000000000000)) * (126 / 100) + 8 * ((47754307 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12504 161) (d.f1 12504 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12504 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12504 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12504 161) (d.f1 12504 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12504 161) (d.w1 12504 161) (d.w2 12504 161)
  have hwexpr0 : 0 ≤ d.w0 12504 161 + d.w1 12504 161 * √(π / 2) +
      2 * d.w2 12504 161 + energyR16 12504 *
      radiusPolynomialRoot16 (d.w0 12504 161) (d.w1 12504 161) (d.w2 12504 161) := by
    positivity
  constructor
  · change (12504 : ℝ) ^ 8 * (mA 12504 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12504 161) (d.f1 12504 161) d.f2 + locationR16 12504 *
        radiusPolynomialRoot16 (d.f0 12504 161) (d.f1 12504 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12504 : ℝ) ^ 8 * (mA 12504 : ℝ) ^ 8 *
        ((((2382208391 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2382208391 / 500000000000000000)) * ((317897999 / 200000000000000000)) * (126 / 100) +
          2 * (((317897999 / 200000000000000000)) ^ 2 + 2 * ((2382208391 / 500000000000000000)) * ((47754307 / 125000000000000000))) +
          6 * ((317897999 / 200000000000000000)) * ((47754307 / 125000000000000000)) * (126 / 100) + 8 * ((47754307 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12504) *
          (32 * (((2382208391 / 500000000000000000) : ℝ) + (317897999 / 200000000000000000) + (47754307 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12504 : ℝ) ^ 16 *
      (d.w0 12504 161 + d.w1 12504 161 * √(π / 2) + 2 * d.w2 12504 161 +
        energyR16 12504 * radiusPolynomialRoot16 (d.w0 12504 161) (d.w1 12504 161)
          (d.w2 12504 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12504 : ℝ) ^ 16 *
        (((480192217 / 25000000000000000000) : ℝ) + ((341647571 / 25000000000000000000)) * (126 / 100) + 2 * ((31207379 / 6250000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12504) *
          (32 * (((480192217 / 25000000000000000000) : ℝ) + (341647571 / 25000000000000000000) + (31207379 / 6250000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12504

/-! A coarse bound on the actual paper statistics constant at dimension 12505. -/
namespace BstLean.Part266.Row12505
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12503 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12503 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12503 128 ≤ (12757 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12757 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12505) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12505 : ℕ))
    (by norm_num : (12505 : ℕ) ≤ 16384)
  have ht : paperTail256 12505 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12505 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12505 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12505 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12505 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12505 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12503 128 * √(2 / (12505 : ℝ)) *
      (√(12505 : ℝ) + paperT0 12505 + paperTail256 12505) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12505 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12505 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12505 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12503 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12503 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12505 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12505

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12505
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12505 (61 / 100) 161 (17 / (100 * 12505)) (26 / (10 * 12505)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12505 (61 / 100) 161 (17 / (100 * 12505)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (62399083 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1596777839 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5793366157 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12505 / 12505 * (61 / 100)) ^ 4 * inverseRadius8 (12505 - 1) /
            envelopeGap 12505 (61 / 100) 161 (17 / (100 * 12505)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12505

namespace BstLean.Part266.Row12505
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12505 161 ≤ (4763462661 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12505 161 ≤ (1589171849 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (190979017 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12505 161 ≤ (960153873 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12505 161 ≤ (1366262281 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12505 161 ≤ (124799569 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (62399083 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (62399083 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1596777839 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5793366157 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((92177 / 25000000) : ℝ) ≤ √(17 / (100 * 12505) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12505) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2234261991 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3995970269 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12505) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12505) ≤ (113091849 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12505) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12505 * (161 : ℝ) ^ 2 + 26 / (10 * 12505) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12505) : ℝ)) (tA 12505 * 161 ^ 2 + 26 / (10 * 12505)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((92177 / 25000000))) * ((62399083 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((92177 / 25000000)) ^ 3) * ((1596777839 / 1000000000000000000000000))) + ((5793366157 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((92177 / 25000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12505) : ℝ)) d.D d.V d.P (√(tA 12505) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((92177 / 25000000)) ^ 2 * (((2234261991 / 1000000000000000)) * ((3995970269 / 100000000000000000)))) + ((5793366157 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12505) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((92177 / 25000000)) * ((62399083 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12505) : ℝ)) (tA 12505 * 161 ^ 2 + 26 / (10 * 12505)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((62399083 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((92177 / 25000000)) ^ 2) * ((1596777839 / 1000000000000000000000000)) + ((5793366157 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12505) : ℝ)) (√(26 / (10 * 12505) : ℝ)) d.D d.V d.P (√(tA 12505) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((92177 / 25000000)) * (((2234261991 / 1000000000000000)) * ((3995970269 / 100000000000000000))) + ((5793366157 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12505) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((62399083 / 12500000000000000000) : ℝ) + ((5793366157 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12505

namespace BstLean.Part266.Row12505
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12505 161 ∧
    0 ≤ (tableEnvelope C).f1 12505 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12505 161 ∧
    0 ≤ (tableEnvelope C).w1 12505 161 ∧ 0 ≤ (tableEnvelope C).w2 12505 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12505 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12505 161 ∧ 0 ≤ d.f1 12505 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12505 161 ∧ 0 ≤ d.w1 12505 161 ∧ 0 ≤ d.w2 12505 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12505 ≤ 2 * (228 / 100 : ℝ) / 12505 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12505 ≤ 2 * (370 / 100 : ℝ) / 12505 := by
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
    (completeRAData (tableEnvelope C) 12505 161).locationBound 12505 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12505 161).energyBound 12505 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12505 161) (d.f1 12505 161) d.f2 ≤
      32 * (((4763462661 / 1000000000000000000) : ℝ) + (1589171849 / 1000000000000000000) + (190979017 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12505 161) (d.w1 12505 161)
      (d.w2 12505 161) ≤
      32 * (((960153873 / 50000000000000000000) : ℝ) + (1366262281 / 100000000000000000000) + (124799569 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12505 161) (d.f1 12505 161) d.f2 ≤
      ((4763462661 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4763462661 / 1000000000000000000)) * ((1589171849 / 1000000000000000000)) * (126 / 100) +
      2 * (((1589171849 / 1000000000000000000)) ^ 2 + 2 * ((4763462661 / 1000000000000000000)) * ((190979017 / 500000000000000000))) +
      6 * ((1589171849 / 1000000000000000000)) * ((190979017 / 500000000000000000)) * (126 / 100) + 8 * ((190979017 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12505 161) (d.f1 12505 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12505 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12505 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12505 161) (d.f1 12505 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12505 161) (d.w1 12505 161) (d.w2 12505 161)
  have hwexpr0 : 0 ≤ d.w0 12505 161 + d.w1 12505 161 * √(π / 2) +
      2 * d.w2 12505 161 + energyR16 12505 *
      radiusPolynomialRoot16 (d.w0 12505 161) (d.w1 12505 161) (d.w2 12505 161) := by
    positivity
  constructor
  · change (12505 : ℝ) ^ 8 * (mA 12505 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12505 161) (d.f1 12505 161) d.f2 + locationR16 12505 *
        radiusPolynomialRoot16 (d.f0 12505 161) (d.f1 12505 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12505 : ℝ) ^ 8 * (mA 12505 : ℝ) ^ 8 *
        ((((4763462661 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4763462661 / 1000000000000000000)) * ((1589171849 / 1000000000000000000)) * (126 / 100) +
          2 * (((1589171849 / 1000000000000000000)) ^ 2 + 2 * ((4763462661 / 1000000000000000000)) * ((190979017 / 500000000000000000))) +
          6 * ((1589171849 / 1000000000000000000)) * ((190979017 / 500000000000000000)) * (126 / 100) + 8 * ((190979017 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12505) *
          (32 * (((4763462661 / 1000000000000000000) : ℝ) + (1589171849 / 1000000000000000000) + (190979017 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12505 : ℝ) ^ 16 *
      (d.w0 12505 161 + d.w1 12505 161 * √(π / 2) + 2 * d.w2 12505 161 +
        energyR16 12505 * radiusPolynomialRoot16 (d.w0 12505 161) (d.w1 12505 161)
          (d.w2 12505 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12505 : ℝ) ^ 16 *
        (((960153873 / 50000000000000000000) : ℝ) + ((1366262281 / 100000000000000000000)) * (126 / 100) + 2 * ((124799569 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12505) *
          (32 * (((960153873 / 50000000000000000000) : ℝ) + (1366262281 / 100000000000000000000) + (124799569 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12505

/-! A coarse bound on the actual paper statistics constant at dimension 12506. -/
namespace BstLean.Part266.Row12506
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12504 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12504 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12504 128 ≤ (12758 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12758 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12506) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12506 : ℕ))
    (by norm_num : (12506 : ℕ) ≤ 16384)
  have ht : paperTail256 12506 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12506 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12506 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12506 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12506 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12506 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12504 128 * √(2 / (12506 : ℝ)) *
      (√(12506 : ℝ) + paperT0 12506 + paperTail256 12506) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12506 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12506 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12506 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12504 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12504 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12506 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12506

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12506
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12506 (61 / 100) 161 (17 / (100 * 12506)) (26 / (10 * 12506)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12506 (61 / 100) 161 (17 / (100 * 12506)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (499072919 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (399066789 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1447406227 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12506 / 12506 * (61 / 100)) ^ 4 * inverseRadius8 (12506 - 1) /
            envelopeGap 12506 (61 / 100) 161 (17 / (100 * 12506)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12506

namespace BstLean.Part266.Row12506
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12506 161 ≤ (4762508873 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12506 161 ≤ (99303363 / 62500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (95470409 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12506 161 ≤ (383969357 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12506 161 ≤ (136593439 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 12506 161 ≤ (3899051 / 781250000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (499072919 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (499072919 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (399066789 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1447406227 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3686933 / 1000000000) : ℝ) ≤ √(17 / (100 * 12506) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12506) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1116997 / 500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9988328051 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12506) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12506) ≤ (56541403 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12506) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12506 * (161 : ℝ) ^ 2 + 26 / (10 * 12506) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12506) : ℝ)) (tA 12506 * 161 ^ 2 + 26 / (10 * 12506)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3686933 / 1000000000))) * ((499072919 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3686933 / 1000000000)) ^ 3) * ((399066789 / 250000000000000000000000))) + ((1447406227 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3686933 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12506) : ℝ)) d.D d.V d.P (√(tA 12506) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3686933 / 1000000000)) ^ 2 * (((1116997 / 500000000000)) * ((9988328051 / 250000000000000000)))) + ((1447406227 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12506) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3686933 / 1000000000)) * ((499072919 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12506) : ℝ)) (tA 12506 * 161 ^ 2 + 26 / (10 * 12506)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((499072919 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3686933 / 1000000000)) ^ 2) * ((399066789 / 250000000000000000000000)) + ((1447406227 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12506) : ℝ)) (√(26 / (10 * 12506) : ℝ)) d.D d.V d.P (√(tA 12506) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3686933 / 1000000000)) * (((1116997 / 500000000000)) * ((9988328051 / 250000000000000000))) + ((1447406227 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12506) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((499072919 / 100000000000000000000) : ℝ) + ((1447406227 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12506

namespace BstLean.Part266.Row12506
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12506 161 ∧
    0 ≤ (tableEnvelope C).f1 12506 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12506 161 ∧
    0 ≤ (tableEnvelope C).w1 12506 161 ∧ 0 ≤ (tableEnvelope C).w2 12506 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12506 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12506 161 ∧ 0 ≤ d.f1 12506 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12506 161 ∧ 0 ≤ d.w1 12506 161 ∧ 0 ≤ d.w2 12506 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12506 ≤ 2 * (228 / 100 : ℝ) / 12506 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12506 ≤ 2 * (370 / 100 : ℝ) / 12506 := by
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
    (completeRAData (tableEnvelope C) 12506 161).locationBound 12506 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12506 161).energyBound 12506 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12506 161) (d.f1 12506 161) d.f2 ≤
      32 * (((4762508873 / 1000000000000000000) : ℝ) + (99303363 / 62500000000000000) + (95470409 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12506 161) (d.w1 12506 161)
      (d.w2 12506 161) ≤
      32 * (((383969357 / 20000000000000000000) : ℝ) + (136593439 / 10000000000000000000) + (3899051 / 781250000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12506 161) (d.f1 12506 161) d.f2 ≤
      ((4762508873 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4762508873 / 1000000000000000000)) * ((99303363 / 62500000000000000)) * (126 / 100) +
      2 * (((99303363 / 62500000000000000)) ^ 2 + 2 * ((4762508873 / 1000000000000000000)) * ((95470409 / 250000000000000000))) +
      6 * ((99303363 / 62500000000000000)) * ((95470409 / 250000000000000000)) * (126 / 100) + 8 * ((95470409 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12506 161) (d.f1 12506 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12506 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12506 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12506 161) (d.f1 12506 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12506 161) (d.w1 12506 161) (d.w2 12506 161)
  have hwexpr0 : 0 ≤ d.w0 12506 161 + d.w1 12506 161 * √(π / 2) +
      2 * d.w2 12506 161 + energyR16 12506 *
      radiusPolynomialRoot16 (d.w0 12506 161) (d.w1 12506 161) (d.w2 12506 161) := by
    positivity
  constructor
  · change (12506 : ℝ) ^ 8 * (mA 12506 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12506 161) (d.f1 12506 161) d.f2 + locationR16 12506 *
        radiusPolynomialRoot16 (d.f0 12506 161) (d.f1 12506 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12506 : ℝ) ^ 8 * (mA 12506 : ℝ) ^ 8 *
        ((((4762508873 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4762508873 / 1000000000000000000)) * ((99303363 / 62500000000000000)) * (126 / 100) +
          2 * (((99303363 / 62500000000000000)) ^ 2 + 2 * ((4762508873 / 1000000000000000000)) * ((95470409 / 250000000000000000))) +
          6 * ((99303363 / 62500000000000000)) * ((95470409 / 250000000000000000)) * (126 / 100) + 8 * ((95470409 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12506) *
          (32 * (((4762508873 / 1000000000000000000) : ℝ) + (99303363 / 62500000000000000) + (95470409 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12506 : ℝ) ^ 16 *
      (d.w0 12506 161 + d.w1 12506 161 * √(π / 2) + 2 * d.w2 12506 161 +
        energyR16 12506 * radiusPolynomialRoot16 (d.w0 12506 161) (d.w1 12506 161)
          (d.w2 12506 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12506 : ℝ) ^ 16 *
        (((383969357 / 20000000000000000000) : ℝ) + ((136593439 / 10000000000000000000)) * (126 / 100) + 2 * ((3899051 / 781250000000000000)) +
          (2 * (370 / 100 : ℝ) / 12506) *
          (32 * (((383969357 / 20000000000000000000) : ℝ) + (136593439 / 10000000000000000000) + (3899051 / 781250000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12506

/-! A coarse bound on the actual paper statistics constant at dimension 12507. -/
namespace BstLean.Part266.Row12507
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12505 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12505 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12505 128 ≤ (12759 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12759 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12507) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12507 : ℕ))
    (by norm_num : (12507 : ℕ) ≤ 16384)
  have ht : paperTail256 12507 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12507 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12507 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12507 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12507 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12507 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12505 128 * √(2 / (12507 : ℝ)) *
      (√(12507 : ℝ) + paperT0 12507 + paperTail256 12507) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12507 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12507 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12507 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12505 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12505 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12507 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12507

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12507
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12507 (61 / 100) 161 (17 / (100 * 12507)) (26 / (10 * 12507)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12507 (61 / 100) 161 (17 / (100 * 12507)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (124738303 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1595756677 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5785886379 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12507 / 12507 * (61 / 100)) ^ 4 * inverseRadius8 (12507 - 1) /
            envelopeGap 12507 (61 / 100) 161 (17 / (100 * 12507)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12507

namespace BstLean.Part266.Row12507
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12507 161 ≤ (952311829 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12507 161 ≤ (1588536733 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (76361073 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12507 161 ≤ (479846689 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12507 161 ≤ (1365606981 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12507 161 ≤ (498958817 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (124738303 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (124738303 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1595756677 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5785886379 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((737357 / 200000000) : ℝ) ≤ √(17 / (100 * 12507) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12507) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1116863031 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39946923249 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12507) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12507) ≤ (28268441 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12507) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12507 * (161 : ℝ) ^ 2 + 26 / (10 * 12507) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12507) : ℝ)) (tA 12507 * 161 ^ 2 + 26 / (10 * 12507)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((737357 / 200000000))) * ((124738303 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((737357 / 200000000)) ^ 3) * ((1595756677 / 1000000000000000000000000))) + ((5785886379 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((737357 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12507) : ℝ)) d.D d.V d.P (√(tA 12507) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((737357 / 200000000)) ^ 2 * (((1116863031 / 500000000000000)) * ((39946923249 / 1000000000000000000)))) + ((5785886379 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12507) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((737357 / 200000000)) * ((124738303 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12507) : ℝ)) (tA 12507 * 161 ^ 2 + 26 / (10 * 12507)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((124738303 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((737357 / 200000000)) ^ 2) * ((1595756677 / 1000000000000000000000000)) + ((5785886379 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12507) : ℝ)) (√(26 / (10 * 12507) : ℝ)) d.D d.V d.P (√(tA 12507) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((737357 / 200000000)) * (((1116863031 / 500000000000000)) * ((39946923249 / 1000000000000000000))) + ((5785886379 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12507) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((124738303 / 25000000000000000000) : ℝ) + ((5785886379 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12507

namespace BstLean.Part266.Row12507
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12507 161 ∧
    0 ≤ (tableEnvelope C).f1 12507 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12507 161 ∧
    0 ≤ (tableEnvelope C).w1 12507 161 ∧ 0 ≤ (tableEnvelope C).w2 12507 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12507 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12507 161 ∧ 0 ≤ d.f1 12507 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12507 161 ∧ 0 ≤ d.w1 12507 161 ∧ 0 ≤ d.w2 12507 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12507 ≤ 2 * (228 / 100 : ℝ) / 12507 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12507 ≤ 2 * (370 / 100 : ℝ) / 12507 := by
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
    (completeRAData (tableEnvelope C) 12507 161).locationBound 12507 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12507 161).energyBound 12507 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12507 161) (d.f1 12507 161) d.f2 ≤
      32 * (((952311829 / 200000000000000000) : ℝ) + (1588536733 / 1000000000000000000) + (76361073 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12507 161) (d.w1 12507 161)
      (d.w2 12507 161) ≤
      32 * (((479846689 / 25000000000000000000) : ℝ) + (1365606981 / 100000000000000000000) + (498958817 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12507 161) (d.f1 12507 161) d.f2 ≤
      ((952311829 / 200000000000000000) : ℝ) ^ 2 + 2 * ((952311829 / 200000000000000000)) * ((1588536733 / 1000000000000000000)) * (126 / 100) +
      2 * (((1588536733 / 1000000000000000000)) ^ 2 + 2 * ((952311829 / 200000000000000000)) * ((76361073 / 200000000000000000))) +
      6 * ((1588536733 / 1000000000000000000)) * ((76361073 / 200000000000000000)) * (126 / 100) + 8 * ((76361073 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12507 161) (d.f1 12507 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12507 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12507 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12507 161) (d.f1 12507 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12507 161) (d.w1 12507 161) (d.w2 12507 161)
  have hwexpr0 : 0 ≤ d.w0 12507 161 + d.w1 12507 161 * √(π / 2) +
      2 * d.w2 12507 161 + energyR16 12507 *
      radiusPolynomialRoot16 (d.w0 12507 161) (d.w1 12507 161) (d.w2 12507 161) := by
    positivity
  constructor
  · change (12507 : ℝ) ^ 8 * (mA 12507 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12507 161) (d.f1 12507 161) d.f2 + locationR16 12507 *
        radiusPolynomialRoot16 (d.f0 12507 161) (d.f1 12507 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12507 : ℝ) ^ 8 * (mA 12507 : ℝ) ^ 8 *
        ((((952311829 / 200000000000000000) : ℝ) ^ 2 + 2 * ((952311829 / 200000000000000000)) * ((1588536733 / 1000000000000000000)) * (126 / 100) +
          2 * (((1588536733 / 1000000000000000000)) ^ 2 + 2 * ((952311829 / 200000000000000000)) * ((76361073 / 200000000000000000))) +
          6 * ((1588536733 / 1000000000000000000)) * ((76361073 / 200000000000000000)) * (126 / 100) + 8 * ((76361073 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12507) *
          (32 * (((952311829 / 200000000000000000) : ℝ) + (1588536733 / 1000000000000000000) + (76361073 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12507 : ℝ) ^ 16 *
      (d.w0 12507 161 + d.w1 12507 161 * √(π / 2) + 2 * d.w2 12507 161 +
        energyR16 12507 * radiusPolynomialRoot16 (d.w0 12507 161) (d.w1 12507 161)
          (d.w2 12507 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12507 : ℝ) ^ 16 *
        (((479846689 / 25000000000000000000) : ℝ) + ((1365606981 / 100000000000000000000)) * (126 / 100) + 2 * ((498958817 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12507) *
          (32 * (((479846689 / 25000000000000000000) : ℝ) + (1365606981 / 100000000000000000000) + (498958817 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12507

/-! A coarse bound on the actual paper statistics constant at dimension 12508. -/
namespace BstLean.Part266.Row12508
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12506 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12506 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12506 128 ≤ (12760 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12760 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12508) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12508 : ℕ))
    (by norm_num : (12508 : ℕ) ≤ 16384)
  have ht : paperTail256 12508 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12508 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12508 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12508 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12508 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12508 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12506 128 * √(2 / (12508 : ℝ)) *
      (√(12508 : ℝ) + paperT0 12508 + paperTail256 12508) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12508 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12508 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12508 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12506 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12506 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12508 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12508

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12508
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12508 (61 / 100) 161 (17 / (100 * 12508)) (26 / (10 * 12508)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12508 (61 / 100) 161 (17 / (100 * 12508)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (498833543 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (797623201 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (578215057 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12508 / 12508 * (61 / 100)) ^ 4 * inverseRadius8 (12508 - 1) /
            envelopeGap 12508 (61 / 100) 161 (17 / (100 * 12508)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12508

namespace BstLean.Part266.Row12508
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12508 161 ≤ (4760606021 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12508 161 ≤ (15882189 / 10000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (381729013 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12508 161 ≤ (479731529 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12508 161 ≤ (1365279313 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12508 161 ≤ (99767829 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (498833543 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (498833543 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (797623201 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (578215057 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1843319 / 500000000) : ℝ) ≤ √(17 / (100 * 12508) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12508) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1116729089 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19970267913 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12508) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12508) ≤ (28266181 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12508) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12508 * (161 : ℝ) ^ 2 + 26 / (10 * 12508) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12508) : ℝ)) (tA 12508 * 161 ^ 2 + 26 / (10 * 12508)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1843319 / 500000000))) * ((498833543 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1843319 / 500000000)) ^ 3) * ((797623201 / 500000000000000000000000))) + ((578215057 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1843319 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12508) : ℝ)) d.D d.V d.P (√(tA 12508) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1843319 / 500000000)) ^ 2 * (((1116729089 / 500000000000000)) * ((19970267913 / 500000000000000000)))) + ((578215057 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12508) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1843319 / 500000000)) * ((498833543 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12508) : ℝ)) (tA 12508 * 161 ^ 2 + 26 / (10 * 12508)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((498833543 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1843319 / 500000000)) ^ 2) * ((797623201 / 500000000000000000000000)) + ((578215057 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12508) : ℝ)) (√(26 / (10 * 12508) : ℝ)) d.D d.V d.P (√(tA 12508) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1843319 / 500000000)) * (((1116729089 / 500000000000000)) * ((19970267913 / 500000000000000000))) + ((578215057 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12508) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((498833543 / 100000000000000000000) : ℝ) + ((578215057 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12508

namespace BstLean.Part266.Row12508
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12508 161 ∧
    0 ≤ (tableEnvelope C).f1 12508 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12508 161 ∧
    0 ≤ (tableEnvelope C).w1 12508 161 ∧ 0 ≤ (tableEnvelope C).w2 12508 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12508 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12508 161 ∧ 0 ≤ d.f1 12508 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12508 161 ∧ 0 ≤ d.w1 12508 161 ∧ 0 ≤ d.w2 12508 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12508 ≤ 2 * (228 / 100 : ℝ) / 12508 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12508 ≤ 2 * (370 / 100 : ℝ) / 12508 := by
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
    (completeRAData (tableEnvelope C) 12508 161).locationBound 12508 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12508 161).energyBound 12508 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12508 161) (d.f1 12508 161) d.f2 ≤
      32 * (((4760606021 / 1000000000000000000) : ℝ) + (15882189 / 10000000000000000) + (381729013 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12508 161) (d.w1 12508 161)
      (d.w2 12508 161) ≤
      32 * (((479731529 / 25000000000000000000) : ℝ) + (1365279313 / 100000000000000000000) + (99767829 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12508 161) (d.f1 12508 161) d.f2 ≤
      ((4760606021 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4760606021 / 1000000000000000000)) * ((15882189 / 10000000000000000)) * (126 / 100) +
      2 * (((15882189 / 10000000000000000)) ^ 2 + 2 * ((4760606021 / 1000000000000000000)) * ((381729013 / 1000000000000000000))) +
      6 * ((15882189 / 10000000000000000)) * ((381729013 / 1000000000000000000)) * (126 / 100) + 8 * ((381729013 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12508 161) (d.f1 12508 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12508 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12508 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12508 161) (d.f1 12508 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12508 161) (d.w1 12508 161) (d.w2 12508 161)
  have hwexpr0 : 0 ≤ d.w0 12508 161 + d.w1 12508 161 * √(π / 2) +
      2 * d.w2 12508 161 + energyR16 12508 *
      radiusPolynomialRoot16 (d.w0 12508 161) (d.w1 12508 161) (d.w2 12508 161) := by
    positivity
  constructor
  · change (12508 : ℝ) ^ 8 * (mA 12508 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12508 161) (d.f1 12508 161) d.f2 + locationR16 12508 *
        radiusPolynomialRoot16 (d.f0 12508 161) (d.f1 12508 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12508 : ℝ) ^ 8 * (mA 12508 : ℝ) ^ 8 *
        ((((4760606021 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4760606021 / 1000000000000000000)) * ((15882189 / 10000000000000000)) * (126 / 100) +
          2 * (((15882189 / 10000000000000000)) ^ 2 + 2 * ((4760606021 / 1000000000000000000)) * ((381729013 / 1000000000000000000))) +
          6 * ((15882189 / 10000000000000000)) * ((381729013 / 1000000000000000000)) * (126 / 100) + 8 * ((381729013 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12508) *
          (32 * (((4760606021 / 1000000000000000000) : ℝ) + (15882189 / 10000000000000000) + (381729013 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12508 : ℝ) ^ 16 *
      (d.w0 12508 161 + d.w1 12508 161 * √(π / 2) + 2 * d.w2 12508 161 +
        energyR16 12508 * radiusPolynomialRoot16 (d.w0 12508 161) (d.w1 12508 161)
          (d.w2 12508 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12508 : ℝ) ^ 16 *
        (((479731529 / 25000000000000000000) : ℝ) + ((1365279313 / 100000000000000000000)) * (126 / 100) + 2 * ((99767829 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12508) *
          (32 * (((479731529 / 25000000000000000000) : ℝ) + (1365279313 / 100000000000000000000) + (99767829 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12508

/-! A coarse bound on the actual paper statistics constant at dimension 12509. -/
namespace BstLean.Part266.Row12509
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12507 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12507 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12507 128 ≤ (12761 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12761 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12509) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12509 : ℕ))
    (by norm_num : (12509 : ℕ) ≤ 16384)
  have ht : paperTail256 12509 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12509 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12509 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12509 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12509 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12509 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12507 128 * √(2 / (12509 : ℝ)) *
      (√(12509 : ℝ) + paperT0 12509 + paperTail256 12509) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12509 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12509 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12509 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12507 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12507 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12509 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12509

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12509
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12509 (61 / 100) 161 (17 / (100 * 12509)) (26 / (10 * 12509)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12509 (61 / 100) 161 (17 / (100 * 12509)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (62339239 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (398684083 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1444604369 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12509 / 12509 * (61 / 100)) ^ 4 * inverseRadius8 (12509 - 1) /
            envelopeGap 12509 (61 / 100) 161 (17 / (100 * 12509)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12509

namespace BstLean.Part266.Row12509
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12509 161 ≤ (4759656959 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12509 161 ≤ (99243877 / 62500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (95413197 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12509 161 ≤ (1918466409 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12509 161 ≤ (682476063 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12509 161 ≤ (49871951 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (62339239 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (62339239 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (398684083 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1444604369 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((368649 / 100000000) : ℝ) ≤ √(17 / (100 * 12509) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12509) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1116595173 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9983537487 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12509) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12509) ≤ (22611137 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12509) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12509 * (161 : ℝ) ^ 2 + 26 / (10 * 12509) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12509) : ℝ)) (tA 12509 * 161 ^ 2 + 26 / (10 * 12509)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((368649 / 100000000))) * ((62339239 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((368649 / 100000000)) ^ 3) * ((398684083 / 250000000000000000000000))) + ((1444604369 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((368649 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12509) : ℝ)) d.D d.V d.P (√(tA 12509) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((368649 / 100000000)) ^ 2 * (((1116595173 / 500000000000000)) * ((9983537487 / 250000000000000000)))) + ((1444604369 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12509) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((368649 / 100000000)) * ((62339239 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12509) : ℝ)) (tA 12509 * 161 ^ 2 + 26 / (10 * 12509)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((62339239 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((368649 / 100000000)) ^ 2) * ((398684083 / 250000000000000000000000)) + ((1444604369 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12509) : ℝ)) (√(26 / (10 * 12509) : ℝ)) d.D d.V d.P (√(tA 12509) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((368649 / 100000000)) * (((1116595173 / 500000000000000)) * ((9983537487 / 250000000000000000))) + ((1444604369 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12509) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((62339239 / 12500000000000000000) : ℝ) + ((1444604369 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12509

namespace BstLean.Part266.Row12509
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12509 161 ∧
    0 ≤ (tableEnvelope C).f1 12509 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12509 161 ∧
    0 ≤ (tableEnvelope C).w1 12509 161 ∧ 0 ≤ (tableEnvelope C).w2 12509 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12509 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12509 161 ∧ 0 ≤ d.f1 12509 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12509 161 ∧ 0 ≤ d.w1 12509 161 ∧ 0 ≤ d.w2 12509 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12509 ≤ 2 * (228 / 100 : ℝ) / 12509 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12509 ≤ 2 * (370 / 100 : ℝ) / 12509 := by
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
    (completeRAData (tableEnvelope C) 12509 161).locationBound 12509 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12509 161).energyBound 12509 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12509 161) (d.f1 12509 161) d.f2 ≤
      32 * (((4759656959 / 1000000000000000000) : ℝ) + (99243877 / 62500000000000000) + (95413197 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12509 161) (d.w1 12509 161)
      (d.w2 12509 161) ≤
      32 * (((1918466409 / 100000000000000000000) : ℝ) + (682476063 / 50000000000000000000) + (49871951 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12509 161) (d.f1 12509 161) d.f2 ≤
      ((4759656959 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4759656959 / 1000000000000000000)) * ((99243877 / 62500000000000000)) * (126 / 100) +
      2 * (((99243877 / 62500000000000000)) ^ 2 + 2 * ((4759656959 / 1000000000000000000)) * ((95413197 / 250000000000000000))) +
      6 * ((99243877 / 62500000000000000)) * ((95413197 / 250000000000000000)) * (126 / 100) + 8 * ((95413197 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12509 161) (d.f1 12509 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12509 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12509 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12509 161) (d.f1 12509 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12509 161) (d.w1 12509 161) (d.w2 12509 161)
  have hwexpr0 : 0 ≤ d.w0 12509 161 + d.w1 12509 161 * √(π / 2) +
      2 * d.w2 12509 161 + energyR16 12509 *
      radiusPolynomialRoot16 (d.w0 12509 161) (d.w1 12509 161) (d.w2 12509 161) := by
    positivity
  constructor
  · change (12509 : ℝ) ^ 8 * (mA 12509 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12509 161) (d.f1 12509 161) d.f2 + locationR16 12509 *
        radiusPolynomialRoot16 (d.f0 12509 161) (d.f1 12509 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12509 : ℝ) ^ 8 * (mA 12509 : ℝ) ^ 8 *
        ((((4759656959 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4759656959 / 1000000000000000000)) * ((99243877 / 62500000000000000)) * (126 / 100) +
          2 * (((99243877 / 62500000000000000)) ^ 2 + 2 * ((4759656959 / 1000000000000000000)) * ((95413197 / 250000000000000000))) +
          6 * ((99243877 / 62500000000000000)) * ((95413197 / 250000000000000000)) * (126 / 100) + 8 * ((95413197 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12509) *
          (32 * (((4759656959 / 1000000000000000000) : ℝ) + (99243877 / 62500000000000000) + (95413197 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12509 : ℝ) ^ 16 *
      (d.w0 12509 161 + d.w1 12509 161 * √(π / 2) + 2 * d.w2 12509 161 +
        energyR16 12509 * radiusPolynomialRoot16 (d.w0 12509 161) (d.w1 12509 161)
          (d.w2 12509 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12509 : ℝ) ^ 16 *
        (((1918466409 / 100000000000000000000) : ℝ) + ((682476063 / 50000000000000000000)) * (126 / 100) + 2 * ((49871951 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12509) *
          (32 * (((1918466409 / 100000000000000000000) : ℝ) + (682476063 / 50000000000000000000) + (49871951 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12509

/-! A coarse bound on the actual paper statistics constant at dimension 12510. -/
namespace BstLean.Part266.Row12510
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12508 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12508 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12508 128 ≤ (12762 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12762 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12510) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12510 : ℕ))
    (by norm_num : (12510 : ℕ) ≤ 16384)
  have ht : paperTail256 12510 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12510 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12510 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12510 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12510 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12510 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12508 128 * √(2 / (12510 : ℝ)) *
      (√(12510 : ℝ) + paperT0 12510 + paperTail256 12510) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12510 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12510 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12510 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12508 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12508 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12510 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12510

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12510
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12510 (61 / 100) 162 (17 / (100 * 12510)) (26 / (10 * 12510)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12510 (61 / 100) 162 (17 / (100 * 12510)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (498594319 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (318845293 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2888719183 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12510 / 12510 * (61 / 100)) ^ 4 * inverseRadius8 (12510 - 1) /
            envelopeGap 12510 (61 / 100) 162 (17 / (100 * 12510)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12510

namespace BstLean.Part266.Row12510
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12510 162 ≤ (9517409 / 2000000000000000)
  f1 : (tableEnvelope C).f1 12510 162 ≤ (1587584407 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (190788241 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12510 162 ≤ (1918006091 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12510 162 ≤ (34115617 / 2500000000000000000)
  w2 : (tableEnvelope C).w2 12510 162 ≤ (124649979 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (498594319 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (498594319 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (318845293 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2888719183 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3686343 / 1000000000) : ℝ) ≤ √(17 / (100 * 12510) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12510) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2232922567 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3992776559 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12510) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12510) ≤ (14130831 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12510) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12510 * (162 : ℝ) ^ 2 + 26 / (10 * 12510) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12510) : ℝ)) (tA 12510 * 162 ^ 2 + 26 / (10 * 12510)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3686343 / 1000000000))) * ((498594319 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3686343 / 1000000000)) ^ 3) * ((318845293 / 200000000000000000000000))) + ((2888719183 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3686343 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12510) : ℝ)) d.D d.V d.P (√(tA 12510) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3686343 / 1000000000)) ^ 2 * (((2232922567 / 1000000000000000)) * ((3992776559 / 100000000000000000)))) + ((2888719183 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12510) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3686343 / 1000000000)) * ((498594319 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12510) : ℝ)) (tA 12510 * 162 ^ 2 + 26 / (10 * 12510)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((498594319 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3686343 / 1000000000)) ^ 2) * ((318845293 / 200000000000000000000000)) + ((2888719183 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12510) : ℝ)) (√(26 / (10 * 12510) : ℝ)) d.D d.V d.P (√(tA 12510) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3686343 / 1000000000)) * (((2232922567 / 1000000000000000)) * ((3992776559 / 100000000000000000))) + ((2888719183 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12510) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((498594319 / 100000000000000000000) : ℝ) + ((2888719183 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12510

namespace BstLean.Part266.Row12510
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12510 162 ∧
    0 ≤ (tableEnvelope C).f1 12510 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12510 162 ∧
    0 ≤ (tableEnvelope C).w1 12510 162 ∧ 0 ≤ (tableEnvelope C).w2 12510 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12510 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12510 162 ∧ 0 ≤ d.f1 12510 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12510 162 ∧ 0 ≤ d.w1 12510 162 ∧ 0 ≤ d.w2 12510 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12510 ≤ 2 * (228 / 100 : ℝ) / 12510 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12510 ≤ 2 * (370 / 100 : ℝ) / 12510 := by
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
    (completeRAData (tableEnvelope C) 12510 162).locationBound 12510 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12510 162).energyBound 12510 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12510 162) (d.f1 12510 162) d.f2 ≤
      32 * (((9517409 / 2000000000000000) : ℝ) + (1587584407 / 1000000000000000000) + (190788241 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12510 162) (d.w1 12510 162)
      (d.w2 12510 162) ≤
      32 * (((1918006091 / 100000000000000000000) : ℝ) + (34115617 / 2500000000000000000) + (124649979 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12510 162) (d.f1 12510 162) d.f2 ≤
      ((9517409 / 2000000000000000) : ℝ) ^ 2 + 2 * ((9517409 / 2000000000000000)) * ((1587584407 / 1000000000000000000)) * (126 / 100) +
      2 * (((1587584407 / 1000000000000000000)) ^ 2 + 2 * ((9517409 / 2000000000000000)) * ((190788241 / 500000000000000000))) +
      6 * ((1587584407 / 1000000000000000000)) * ((190788241 / 500000000000000000)) * (126 / 100) + 8 * ((190788241 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12510 162) (d.f1 12510 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12510 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12510 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12510 162) (d.f1 12510 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12510 162) (d.w1 12510 162) (d.w2 12510 162)
  have hwexpr0 : 0 ≤ d.w0 12510 162 + d.w1 12510 162 * √(π / 2) +
      2 * d.w2 12510 162 + energyR16 12510 *
      radiusPolynomialRoot16 (d.w0 12510 162) (d.w1 12510 162) (d.w2 12510 162) := by
    positivity
  constructor
  · change (12510 : ℝ) ^ 8 * (mA 12510 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12510 162) (d.f1 12510 162) d.f2 + locationR16 12510 *
        radiusPolynomialRoot16 (d.f0 12510 162) (d.f1 12510 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12510 : ℝ) ^ 8 * (mA 12510 : ℝ) ^ 8 *
        ((((9517409 / 2000000000000000) : ℝ) ^ 2 + 2 * ((9517409 / 2000000000000000)) * ((1587584407 / 1000000000000000000)) * (126 / 100) +
          2 * (((1587584407 / 1000000000000000000)) ^ 2 + 2 * ((9517409 / 2000000000000000)) * ((190788241 / 500000000000000000))) +
          6 * ((1587584407 / 1000000000000000000)) * ((190788241 / 500000000000000000)) * (126 / 100) + 8 * ((190788241 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12510) *
          (32 * (((9517409 / 2000000000000000) : ℝ) + (1587584407 / 1000000000000000000) + (190788241 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12510 : ℝ) ^ 16 *
      (d.w0 12510 162 + d.w1 12510 162 * √(π / 2) + 2 * d.w2 12510 162 +
        energyR16 12510 * radiusPolynomialRoot16 (d.w0 12510 162) (d.w1 12510 162)
          (d.w2 12510 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12510 : ℝ) ^ 16 *
        (((1918006091 / 100000000000000000000) : ℝ) + ((34115617 / 2500000000000000000)) * (126 / 100) + 2 * ((124649979 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12510) *
          (32 * (((1918006091 / 100000000000000000000) : ℝ) + (34115617 / 2500000000000000000) + (124649979 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12510

/-! A coarse bound on the actual paper statistics constant at dimension 12511. -/
namespace BstLean.Part266.Row12511
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12509 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12509 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12509 128 ≤ (12763 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12763 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12511) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12511 : ℕ))
    (by norm_num : (12511 : ℕ) ≤ 16384)
  have ht : paperTail256 12511 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12511 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12511 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12511 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12511 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12511 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12509 128 * √(2 / (12511 : ℝ)) *
      (√(12511 : ℝ) + paperT0 12511 + paperTail256 12511) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12511 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12511 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12511 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12509 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12509 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12511 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12511

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12511
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12511 (61 / 100) 162 (17 / (100 * 12511)) (26 / (10 * 12511)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12511 (61 / 100) 162 (17 / (100 * 12511)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (99694953 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1593716801 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5773708481 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12511 / 12511 * (61 / 100)) ^ 4 * inverseRadius8 (12511 - 1) /
            envelopeGap 12511 (61 / 100) 162 (17 / (100 * 12511)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12511

namespace BstLean.Part266.Row12511
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12511 162 ≤ (4757752371 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12511 162 ≤ (793633443 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (1907501 / 5000000000000000)
  w0 : (tableEnvelope C).w0 12511 162 ≤ (958772967 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12511 162 ≤ (272859469 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12511 162 ≤ (249240179 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (99694953 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (99694953 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1593716801 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5773708481 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((921549 / 250000000) : ℝ) ≤ √(17 / (100 * 12511) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12511) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (558163711 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7984276551 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12511) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12511) ≤ (28259403 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12511) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12511 * (162 : ℝ) ^ 2 + 26 / (10 * 12511) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12511) : ℝ)) (tA 12511 * 162 ^ 2 + 26 / (10 * 12511)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((921549 / 250000000))) * ((99694953 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((921549 / 250000000)) ^ 3) * ((1593716801 / 1000000000000000000000000))) + ((5773708481 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((921549 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12511) : ℝ)) d.D d.V d.P (√(tA 12511) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((921549 / 250000000)) ^ 2 * (((558163711 / 250000000000000)) * ((7984276551 / 200000000000000000)))) + ((5773708481 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12511) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((921549 / 250000000)) * ((99694953 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12511) : ℝ)) (tA 12511 * 162 ^ 2 + 26 / (10 * 12511)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((99694953 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((921549 / 250000000)) ^ 2) * ((1593716801 / 1000000000000000000000000)) + ((5773708481 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12511) : ℝ)) (√(26 / (10 * 12511) : ℝ)) d.D d.V d.P (√(tA 12511) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((921549 / 250000000)) * (((558163711 / 250000000000000)) * ((7984276551 / 200000000000000000))) + ((5773708481 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12511) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((99694953 / 20000000000000000000) : ℝ) + ((5773708481 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12511

namespace BstLean.Part266.Row12511
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12511 162 ∧
    0 ≤ (tableEnvelope C).f1 12511 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12511 162 ∧
    0 ≤ (tableEnvelope C).w1 12511 162 ∧ 0 ≤ (tableEnvelope C).w2 12511 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12511 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12511 162 ∧ 0 ≤ d.f1 12511 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12511 162 ∧ 0 ≤ d.w1 12511 162 ∧ 0 ≤ d.w2 12511 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12511 ≤ 2 * (228 / 100 : ℝ) / 12511 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12511 ≤ 2 * (370 / 100 : ℝ) / 12511 := by
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
    (completeRAData (tableEnvelope C) 12511 162).locationBound 12511 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12511 162).energyBound 12511 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12511 162) (d.f1 12511 162) d.f2 ≤
      32 * (((4757752371 / 1000000000000000000) : ℝ) + (793633443 / 500000000000000000) + (1907501 / 5000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12511 162) (d.w1 12511 162)
      (d.w2 12511 162) ≤
      32 * (((958772967 / 50000000000000000000) : ℝ) + (272859469 / 20000000000000000000) + (249240179 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12511 162) (d.f1 12511 162) d.f2 ≤
      ((4757752371 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4757752371 / 1000000000000000000)) * ((793633443 / 500000000000000000)) * (126 / 100) +
      2 * (((793633443 / 500000000000000000)) ^ 2 + 2 * ((4757752371 / 1000000000000000000)) * ((1907501 / 5000000000000000))) +
      6 * ((793633443 / 500000000000000000)) * ((1907501 / 5000000000000000)) * (126 / 100) + 8 * ((1907501 / 5000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12511 162) (d.f1 12511 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12511 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12511 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12511 162) (d.f1 12511 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12511 162) (d.w1 12511 162) (d.w2 12511 162)
  have hwexpr0 : 0 ≤ d.w0 12511 162 + d.w1 12511 162 * √(π / 2) +
      2 * d.w2 12511 162 + energyR16 12511 *
      radiusPolynomialRoot16 (d.w0 12511 162) (d.w1 12511 162) (d.w2 12511 162) := by
    positivity
  constructor
  · change (12511 : ℝ) ^ 8 * (mA 12511 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12511 162) (d.f1 12511 162) d.f2 + locationR16 12511 *
        radiusPolynomialRoot16 (d.f0 12511 162) (d.f1 12511 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12511 : ℝ) ^ 8 * (mA 12511 : ℝ) ^ 8 *
        ((((4757752371 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4757752371 / 1000000000000000000)) * ((793633443 / 500000000000000000)) * (126 / 100) +
          2 * (((793633443 / 500000000000000000)) ^ 2 + 2 * ((4757752371 / 1000000000000000000)) * ((1907501 / 5000000000000000))) +
          6 * ((793633443 / 500000000000000000)) * ((1907501 / 5000000000000000)) * (126 / 100) + 8 * ((1907501 / 5000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12511) *
          (32 * (((4757752371 / 1000000000000000000) : ℝ) + (793633443 / 500000000000000000) + (1907501 / 5000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12511 : ℝ) ^ 16 *
      (d.w0 12511 162 + d.w1 12511 162 * √(π / 2) + 2 * d.w2 12511 162 +
        energyR16 12511 * radiusPolynomialRoot16 (d.w0 12511 162) (d.w1 12511 162)
          (d.w2 12511 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12511 : ℝ) ^ 16 *
        (((958772967 / 50000000000000000000) : ℝ) + ((272859469 / 20000000000000000000)) * (126 / 100) + 2 * ((249240179 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12511) *
          (32 * (((958772967 / 50000000000000000000) : ℝ) + (272859469 / 20000000000000000000) + (249240179 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12511

/-! A coarse bound on the actual paper statistics constant at dimension 12512. -/
namespace BstLean.Part266.Row12512
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12510 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12510 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12510 128 ≤ (12764 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12764 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12512) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12512 : ℕ))
    (by norm_num : (12512 : ℕ) ≤ 16384)
  have ht : paperTail256 12512 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12512 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12512 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12512 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12512 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12512 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12510 128 * √(2 / (12512 : ℝ)) *
      (√(12512 : ℝ) + paperT0 12512 + paperTail256 12512) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12512 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12512 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12512 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12510 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12510 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12512 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12512

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12512
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12512 (61 / 100) 162 (17 / (100 * 12512)) (26 / (10 * 12512)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12512 (61 / 100) 162 (17 / (100 * 12512)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (498355249 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (796603671 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5769981307 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12512 / 12512 * (61 / 100)) ^ 4 * inverseRadius8 (12512 - 1) /
            envelopeGap 12512 (61 / 100) 162 (17 / (100 * 12512)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12512

namespace BstLean.Part266.Row12512
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12512 162 ≤ (297300269 / 62500000000000000)
  f1 : (tableEnvelope C).f1 12512 162 ≤ (158695033 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (95356011 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12512 162 ≤ (479271677 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12512 162 ≤ (340992623 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12512 162 ≤ (498360839 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (498355249 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (498355249 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (796603671 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5769981307 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((115189 / 31250000) : ℝ) ≤ √(17 / (100 * 12512) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12512) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2232387173 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19957500733 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12512) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12512) ≤ (56514289 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12512) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12512 * (162 : ℝ) ^ 2 + 26 / (10 * 12512) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12512) : ℝ)) (tA 12512 * 162 ^ 2 + 26 / (10 * 12512)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((115189 / 31250000))) * ((498355249 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((115189 / 31250000)) ^ 3) * ((796603671 / 500000000000000000000000))) + ((5769981307 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((115189 / 31250000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12512) : ℝ)) d.D d.V d.P (√(tA 12512) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((115189 / 31250000)) ^ 2 * (((2232387173 / 1000000000000000)) * ((19957500733 / 500000000000000000)))) + ((5769981307 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12512) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((115189 / 31250000)) * ((498355249 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12512) : ℝ)) (tA 12512 * 162 ^ 2 + 26 / (10 * 12512)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((498355249 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((115189 / 31250000)) ^ 2) * ((796603671 / 500000000000000000000000)) + ((5769981307 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12512) : ℝ)) (√(26 / (10 * 12512) : ℝ)) d.D d.V d.P (√(tA 12512) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((115189 / 31250000)) * (((2232387173 / 1000000000000000)) * ((19957500733 / 500000000000000000))) + ((5769981307 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12512) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((498355249 / 100000000000000000000) : ℝ) + ((5769981307 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12512

namespace BstLean.Part266.Row12512
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12512 162 ∧
    0 ≤ (tableEnvelope C).f1 12512 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12512 162 ∧
    0 ≤ (tableEnvelope C).w1 12512 162 ∧ 0 ≤ (tableEnvelope C).w2 12512 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12512 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12512 162 ∧ 0 ≤ d.f1 12512 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12512 162 ∧ 0 ≤ d.w1 12512 162 ∧ 0 ≤ d.w2 12512 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12512 ≤ 2 * (228 / 100 : ℝ) / 12512 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12512 ≤ 2 * (370 / 100 : ℝ) / 12512 := by
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
    (completeRAData (tableEnvelope C) 12512 162).locationBound 12512 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12512 162).energyBound 12512 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12512 162) (d.f1 12512 162) d.f2 ≤
      32 * (((297300269 / 62500000000000000) : ℝ) + (158695033 / 100000000000000000) + (95356011 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12512 162) (d.w1 12512 162)
      (d.w2 12512 162) ≤
      32 * (((479271677 / 25000000000000000000) : ℝ) + (340992623 / 25000000000000000000) + (498360839 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12512 162) (d.f1 12512 162) d.f2 ≤
      ((297300269 / 62500000000000000) : ℝ) ^ 2 + 2 * ((297300269 / 62500000000000000)) * ((158695033 / 100000000000000000)) * (126 / 100) +
      2 * (((158695033 / 100000000000000000)) ^ 2 + 2 * ((297300269 / 62500000000000000)) * ((95356011 / 250000000000000000))) +
      6 * ((158695033 / 100000000000000000)) * ((95356011 / 250000000000000000)) * (126 / 100) + 8 * ((95356011 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12512 162) (d.f1 12512 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12512 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12512 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12512 162) (d.f1 12512 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12512 162) (d.w1 12512 162) (d.w2 12512 162)
  have hwexpr0 : 0 ≤ d.w0 12512 162 + d.w1 12512 162 * √(π / 2) +
      2 * d.w2 12512 162 + energyR16 12512 *
      radiusPolynomialRoot16 (d.w0 12512 162) (d.w1 12512 162) (d.w2 12512 162) := by
    positivity
  constructor
  · change (12512 : ℝ) ^ 8 * (mA 12512 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12512 162) (d.f1 12512 162) d.f2 + locationR16 12512 *
        radiusPolynomialRoot16 (d.f0 12512 162) (d.f1 12512 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12512 : ℝ) ^ 8 * (mA 12512 : ℝ) ^ 8 *
        ((((297300269 / 62500000000000000) : ℝ) ^ 2 + 2 * ((297300269 / 62500000000000000)) * ((158695033 / 100000000000000000)) * (126 / 100) +
          2 * (((158695033 / 100000000000000000)) ^ 2 + 2 * ((297300269 / 62500000000000000)) * ((95356011 / 250000000000000000))) +
          6 * ((158695033 / 100000000000000000)) * ((95356011 / 250000000000000000)) * (126 / 100) + 8 * ((95356011 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12512) *
          (32 * (((297300269 / 62500000000000000) : ℝ) + (158695033 / 100000000000000000) + (95356011 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12512 : ℝ) ^ 16 *
      (d.w0 12512 162 + d.w1 12512 162 * √(π / 2) + 2 * d.w2 12512 162 +
        energyR16 12512 * radiusPolynomialRoot16 (d.w0 12512 162) (d.w1 12512 162)
          (d.w2 12512 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12512 : ℝ) ^ 16 *
        (((479271677 / 25000000000000000000) : ℝ) + ((340992623 / 25000000000000000000)) * (126 / 100) + 2 * ((498360839 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12512) *
          (32 * (((479271677 / 25000000000000000000) : ℝ) + (340992623 / 25000000000000000000) + (498360839 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12512

/-! A coarse bound on the actual paper statistics constant at dimension 12513. -/
namespace BstLean.Part266.Row12513
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12511 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12511 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12511 128 ≤ (12765 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12765 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12513) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12513 : ℕ))
    (by norm_num : (12513 : ℕ) ≤ 16384)
  have ht : paperTail256 12513 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12513 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12513 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12513 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12513 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12513 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12511 128 * √(2 / (12513 : ℝ)) *
      (√(12513 : ℝ) + paperT0 12513 + paperTail256 12513) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12513 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12513 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12513 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12511 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12511 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12513 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12513

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12513
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12513 (61 / 100) 162 (17 / (100 * 12513)) (26 / (10 * 12513)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12513 (61 / 100) 162 (17 / (100 * 12513)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (498235771 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (796349043 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2883128421 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12513 / 12513 * (61 / 100)) ^ 4 * inverseRadius8 (12513 - 1) /
            envelopeGap 12513 (61 / 100) 162 (17 / (100 * 12513)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12513

namespace BstLean.Part266.Row12513
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12513 162 ≤ (4755852841 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12513 162 ≤ (1586633017 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (11917119 / 31250000000000000)
  w0 : (tableEnvelope C).w0 12513 162 ≤ (239578359 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12513 162 ≤ (1363643379 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12513 162 ≤ (498241357 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (498235771 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (498235771 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (796349043 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2883128421 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3685901 / 1000000000) : ℝ) ≤ √(17 / (100 * 12513) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12513) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (558029889 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39908621701 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12513) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12513) ≤ (22603909 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12513) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12513 * (162 : ℝ) ^ 2 + 26 / (10 * 12513) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12513) : ℝ)) (tA 12513 * 162 ^ 2 + 26 / (10 * 12513)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3685901 / 1000000000))) * ((498235771 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3685901 / 1000000000)) ^ 3) * ((796349043 / 500000000000000000000000))) + ((2883128421 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3685901 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12513) : ℝ)) d.D d.V d.P (√(tA 12513) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3685901 / 1000000000)) ^ 2 * (((558029889 / 250000000000000)) * ((39908621701 / 1000000000000000000)))) + ((2883128421 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12513) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3685901 / 1000000000)) * ((498235771 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12513) : ℝ)) (tA 12513 * 162 ^ 2 + 26 / (10 * 12513)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((498235771 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3685901 / 1000000000)) ^ 2) * ((796349043 / 500000000000000000000000)) + ((2883128421 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12513) : ℝ)) (√(26 / (10 * 12513) : ℝ)) d.D d.V d.P (√(tA 12513) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3685901 / 1000000000)) * (((558029889 / 250000000000000)) * ((39908621701 / 1000000000000000000))) + ((2883128421 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12513) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((498235771 / 100000000000000000000) : ℝ) + ((2883128421 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12513

namespace BstLean.Part266.Row12513
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12513 162 ∧
    0 ≤ (tableEnvelope C).f1 12513 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12513 162 ∧
    0 ≤ (tableEnvelope C).w1 12513 162 ∧ 0 ≤ (tableEnvelope C).w2 12513 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12513 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12513 162 ∧ 0 ≤ d.f1 12513 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12513 162 ∧ 0 ≤ d.w1 12513 162 ∧ 0 ≤ d.w2 12513 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12513 ≤ 2 * (228 / 100 : ℝ) / 12513 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12513 ≤ 2 * (370 / 100 : ℝ) / 12513 := by
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
    (completeRAData (tableEnvelope C) 12513 162).locationBound 12513 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12513 162).energyBound 12513 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12513 162) (d.f1 12513 162) d.f2 ≤
      32 * (((4755852841 / 1000000000000000000) : ℝ) + (1586633017 / 1000000000000000000) + (11917119 / 31250000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12513 162) (d.w1 12513 162)
      (d.w2 12513 162) ≤
      32 * (((239578359 / 12500000000000000000) : ℝ) + (1363643379 / 100000000000000000000) + (498241357 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12513 162) (d.f1 12513 162) d.f2 ≤
      ((4755852841 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4755852841 / 1000000000000000000)) * ((1586633017 / 1000000000000000000)) * (126 / 100) +
      2 * (((1586633017 / 1000000000000000000)) ^ 2 + 2 * ((4755852841 / 1000000000000000000)) * ((11917119 / 31250000000000000))) +
      6 * ((1586633017 / 1000000000000000000)) * ((11917119 / 31250000000000000)) * (126 / 100) + 8 * ((11917119 / 31250000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12513 162) (d.f1 12513 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12513 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12513 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12513 162) (d.f1 12513 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12513 162) (d.w1 12513 162) (d.w2 12513 162)
  have hwexpr0 : 0 ≤ d.w0 12513 162 + d.w1 12513 162 * √(π / 2) +
      2 * d.w2 12513 162 + energyR16 12513 *
      radiusPolynomialRoot16 (d.w0 12513 162) (d.w1 12513 162) (d.w2 12513 162) := by
    positivity
  constructor
  · change (12513 : ℝ) ^ 8 * (mA 12513 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12513 162) (d.f1 12513 162) d.f2 + locationR16 12513 *
        radiusPolynomialRoot16 (d.f0 12513 162) (d.f1 12513 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12513 : ℝ) ^ 8 * (mA 12513 : ℝ) ^ 8 *
        ((((4755852841 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4755852841 / 1000000000000000000)) * ((1586633017 / 1000000000000000000)) * (126 / 100) +
          2 * (((1586633017 / 1000000000000000000)) ^ 2 + 2 * ((4755852841 / 1000000000000000000)) * ((11917119 / 31250000000000000))) +
          6 * ((1586633017 / 1000000000000000000)) * ((11917119 / 31250000000000000)) * (126 / 100) + 8 * ((11917119 / 31250000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12513) *
          (32 * (((4755852841 / 1000000000000000000) : ℝ) + (1586633017 / 1000000000000000000) + (11917119 / 31250000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12513 : ℝ) ^ 16 *
      (d.w0 12513 162 + d.w1 12513 162 * √(π / 2) + 2 * d.w2 12513 162 +
        energyR16 12513 * radiusPolynomialRoot16 (d.w0 12513 162) (d.w1 12513 162)
          (d.w2 12513 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12513 : ℝ) ^ 16 *
        (((239578359 / 12500000000000000000) : ℝ) + ((1363643379 / 100000000000000000000)) * (126 / 100) + 2 * ((498241357 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12513) *
          (32 * (((239578359 / 12500000000000000000) : ℝ) + (1363643379 / 100000000000000000000) + (498241357 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12513

/-! A coarse bound on the actual paper statistics constant at dimension 12514. -/
namespace BstLean.Part266.Row12514
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12512 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12512 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12512 128 ≤ (12766 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12766 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12514) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12514 : ℕ))
    (by norm_num : (12514 : ℕ) ≤ 16384)
  have ht : paperTail256 12514 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12514 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12514 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12514 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12514 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12514 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12512 128 * √(2 / (12514 : ℝ)) *
      (√(12514 : ℝ) + paperT0 12514 + paperTail256 12514) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12514 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12514 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12514 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12512 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12512 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12514 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12514

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12514
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12514 (61 / 100) 162 (17 / (100 * 12514)) (26 / (10 * 12514)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12514 (61 / 100) 162 (17 / (100 * 12514)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (124529083 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1592189033 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1152507017 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12514 / 12514 * (61 / 100)) ^ 4 * inverseRadius8 (12514 - 1) /
            envelopeGap 12514 (61 / 100) 162 (17 / (100 * 12514)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12514

namespace BstLean.Part266.Row12514
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12514 162 ≤ (4754901709 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12514 162 ≤ (1586315809 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (76254319 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12514 162 ≤ (958083599 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12514 162 ≤ (1363316379 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12514 162 ≤ (99624383 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (124529083 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (124529083 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1592189033 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1152507017 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1842877 / 500000000) : ℝ) ≤ √(17 / (100 * 12514) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12514) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1115925997 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39902243459 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12514) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12514) ≤ (56505257 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12514) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12514 * (162 : ℝ) ^ 2 + 26 / (10 * 12514) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12514) : ℝ)) (tA 12514 * 162 ^ 2 + 26 / (10 * 12514)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1842877 / 500000000))) * ((124529083 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1842877 / 500000000)) ^ 3) * ((1592189033 / 1000000000000000000000000))) + ((1152507017 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1842877 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12514) : ℝ)) d.D d.V d.P (√(tA 12514) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1842877 / 500000000)) ^ 2 * (((1115925997 / 500000000000000)) * ((39902243459 / 1000000000000000000)))) + ((1152507017 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12514) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1842877 / 500000000)) * ((124529083 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12514) : ℝ)) (tA 12514 * 162 ^ 2 + 26 / (10 * 12514)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((124529083 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1842877 / 500000000)) ^ 2) * ((1592189033 / 1000000000000000000000000)) + ((1152507017 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12514) : ℝ)) (√(26 / (10 * 12514) : ℝ)) d.D d.V d.P (√(tA 12514) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1842877 / 500000000)) * (((1115925997 / 500000000000000)) * ((39902243459 / 1000000000000000000))) + ((1152507017 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12514) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((124529083 / 25000000000000000000) : ℝ) + ((1152507017 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12514

namespace BstLean.Part266.Row12514
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12514 162 ∧
    0 ≤ (tableEnvelope C).f1 12514 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12514 162 ∧
    0 ≤ (tableEnvelope C).w1 12514 162 ∧ 0 ≤ (tableEnvelope C).w2 12514 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12514 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12514 162 ∧ 0 ≤ d.f1 12514 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12514 162 ∧ 0 ≤ d.w1 12514 162 ∧ 0 ≤ d.w2 12514 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12514 ≤ 2 * (228 / 100 : ℝ) / 12514 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12514 ≤ 2 * (370 / 100 : ℝ) / 12514 := by
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
    (completeRAData (tableEnvelope C) 12514 162).locationBound 12514 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12514 162).energyBound 12514 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12514 162) (d.f1 12514 162) d.f2 ≤
      32 * (((4754901709 / 1000000000000000000) : ℝ) + (1586315809 / 1000000000000000000) + (76254319 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12514 162) (d.w1 12514 162)
      (d.w2 12514 162) ≤
      32 * (((958083599 / 50000000000000000000) : ℝ) + (1363316379 / 100000000000000000000) + (99624383 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12514 162) (d.f1 12514 162) d.f2 ≤
      ((4754901709 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4754901709 / 1000000000000000000)) * ((1586315809 / 1000000000000000000)) * (126 / 100) +
      2 * (((1586315809 / 1000000000000000000)) ^ 2 + 2 * ((4754901709 / 1000000000000000000)) * ((76254319 / 200000000000000000))) +
      6 * ((1586315809 / 1000000000000000000)) * ((76254319 / 200000000000000000)) * (126 / 100) + 8 * ((76254319 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12514 162) (d.f1 12514 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12514 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12514 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12514 162) (d.f1 12514 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12514 162) (d.w1 12514 162) (d.w2 12514 162)
  have hwexpr0 : 0 ≤ d.w0 12514 162 + d.w1 12514 162 * √(π / 2) +
      2 * d.w2 12514 162 + energyR16 12514 *
      radiusPolynomialRoot16 (d.w0 12514 162) (d.w1 12514 162) (d.w2 12514 162) := by
    positivity
  constructor
  · change (12514 : ℝ) ^ 8 * (mA 12514 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12514 162) (d.f1 12514 162) d.f2 + locationR16 12514 *
        radiusPolynomialRoot16 (d.f0 12514 162) (d.f1 12514 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12514 : ℝ) ^ 8 * (mA 12514 : ℝ) ^ 8 *
        ((((4754901709 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4754901709 / 1000000000000000000)) * ((1586315809 / 1000000000000000000)) * (126 / 100) +
          2 * (((1586315809 / 1000000000000000000)) ^ 2 + 2 * ((4754901709 / 1000000000000000000)) * ((76254319 / 200000000000000000))) +
          6 * ((1586315809 / 1000000000000000000)) * ((76254319 / 200000000000000000)) * (126 / 100) + 8 * ((76254319 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12514) *
          (32 * (((4754901709 / 1000000000000000000) : ℝ) + (1586315809 / 1000000000000000000) + (76254319 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12514 : ℝ) ^ 16 *
      (d.w0 12514 162 + d.w1 12514 162 * √(π / 2) + 2 * d.w2 12514 162 +
        energyR16 12514 * radiusPolynomialRoot16 (d.w0 12514 162) (d.w1 12514 162)
          (d.w2 12514 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12514 : ℝ) ^ 16 *
        (((958083599 / 50000000000000000000) : ℝ) + ((1363316379 / 100000000000000000000)) * (126 / 100) + 2 * ((99624383 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12514) *
          (32 * (((958083599 / 50000000000000000000) : ℝ) + (1363316379 / 100000000000000000000) + (99624383 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12514

/-! A coarse bound on the actual paper statistics constant at dimension 12515. -/
namespace BstLean.Part266.Row12515
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12513 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12513 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12513 128 ≤ (12767 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12767 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12515) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12515 : ℕ))
    (by norm_num : (12515 : ℕ) ≤ 16384)
  have ht : paperTail256 12515 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12515 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12515 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12515 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12515 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12515 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12513 128 * √(2 / (12515 : ℝ)) *
      (√(12515 : ℝ) + paperT0 12515 + paperTail256 12515) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12515 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12515 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12515 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12513 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12513 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12515 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12515

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12515
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12515 (61 / 100) 162 (17 / (100 * 12515)) (26 / (10 * 12515)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12515 (61 / 100) 162 (17 / (100 * 12515)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (49799693 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (198960023 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5758816033 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12515 / 12515 * (61 / 100)) ^ 4 * inverseRadius8 (12515 - 1) /
            envelopeGap 12515 (61 / 100) 162 (17 / (100 * 12515)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12515

namespace BstLean.Part266.Row12515
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12515 162 ≤ (475395091 / 100000000000000000)
  f1 : (tableEnvelope C).f1 12515 162 ≤ (1585998703 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (76239081 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12515 162 ≤ (1915707683 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12515 162 ≤ (85186843 / 6250000000000000000)
  w2 : (tableEnvelope C).w2 12515 162 ≤ (498002509 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (49799693 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (49799693 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (198960023 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5758816033 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3685607 / 1000000000) : ℝ) ≤ √(17 / (100 * 12515) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12515) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1115792241 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19947933377 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12515) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12515) ≤ (28250371 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12515) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12515 * (162 : ℝ) ^ 2 + 26 / (10 * 12515) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12515) : ℝ)) (tA 12515 * 162 ^ 2 + 26 / (10 * 12515)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3685607 / 1000000000))) * ((49799693 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3685607 / 1000000000)) ^ 3) * ((198960023 / 125000000000000000000000))) + ((5758816033 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3685607 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12515) : ℝ)) d.D d.V d.P (√(tA 12515) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3685607 / 1000000000)) ^ 2 * (((1115792241 / 500000000000000)) * ((19947933377 / 500000000000000000)))) + ((5758816033 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12515) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3685607 / 1000000000)) * ((49799693 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12515) : ℝ)) (tA 12515 * 162 ^ 2 + 26 / (10 * 12515)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((49799693 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3685607 / 1000000000)) ^ 2) * ((198960023 / 125000000000000000000000)) + ((5758816033 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12515) : ℝ)) (√(26 / (10 * 12515) : ℝ)) d.D d.V d.P (√(tA 12515) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3685607 / 1000000000)) * (((1115792241 / 500000000000000)) * ((19947933377 / 500000000000000000))) + ((5758816033 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12515) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((49799693 / 10000000000000000000) : ℝ) + ((5758816033 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12515

namespace BstLean.Part266.Row12515
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12515 162 ∧
    0 ≤ (tableEnvelope C).f1 12515 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12515 162 ∧
    0 ≤ (tableEnvelope C).w1 12515 162 ∧ 0 ≤ (tableEnvelope C).w2 12515 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12515 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12515 162 ∧ 0 ≤ d.f1 12515 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12515 162 ∧ 0 ≤ d.w1 12515 162 ∧ 0 ≤ d.w2 12515 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12515 ≤ 2 * (228 / 100 : ℝ) / 12515 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12515 ≤ 2 * (370 / 100 : ℝ) / 12515 := by
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
    (completeRAData (tableEnvelope C) 12515 162).locationBound 12515 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12515 162).energyBound 12515 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12515 162) (d.f1 12515 162) d.f2 ≤
      32 * (((475395091 / 100000000000000000) : ℝ) + (1585998703 / 1000000000000000000) + (76239081 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12515 162) (d.w1 12515 162)
      (d.w2 12515 162) ≤
      32 * (((1915707683 / 100000000000000000000) : ℝ) + (85186843 / 6250000000000000000) + (498002509 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12515 162) (d.f1 12515 162) d.f2 ≤
      ((475395091 / 100000000000000000) : ℝ) ^ 2 + 2 * ((475395091 / 100000000000000000)) * ((1585998703 / 1000000000000000000)) * (126 / 100) +
      2 * (((1585998703 / 1000000000000000000)) ^ 2 + 2 * ((475395091 / 100000000000000000)) * ((76239081 / 200000000000000000))) +
      6 * ((1585998703 / 1000000000000000000)) * ((76239081 / 200000000000000000)) * (126 / 100) + 8 * ((76239081 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12515 162) (d.f1 12515 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12515 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12515 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12515 162) (d.f1 12515 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12515 162) (d.w1 12515 162) (d.w2 12515 162)
  have hwexpr0 : 0 ≤ d.w0 12515 162 + d.w1 12515 162 * √(π / 2) +
      2 * d.w2 12515 162 + energyR16 12515 *
      radiusPolynomialRoot16 (d.w0 12515 162) (d.w1 12515 162) (d.w2 12515 162) := by
    positivity
  constructor
  · change (12515 : ℝ) ^ 8 * (mA 12515 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12515 162) (d.f1 12515 162) d.f2 + locationR16 12515 *
        radiusPolynomialRoot16 (d.f0 12515 162) (d.f1 12515 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12515 : ℝ) ^ 8 * (mA 12515 : ℝ) ^ 8 *
        ((((475395091 / 100000000000000000) : ℝ) ^ 2 + 2 * ((475395091 / 100000000000000000)) * ((1585998703 / 1000000000000000000)) * (126 / 100) +
          2 * (((1585998703 / 1000000000000000000)) ^ 2 + 2 * ((475395091 / 100000000000000000)) * ((76239081 / 200000000000000000))) +
          6 * ((1585998703 / 1000000000000000000)) * ((76239081 / 200000000000000000)) * (126 / 100) + 8 * ((76239081 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12515) *
          (32 * (((475395091 / 100000000000000000) : ℝ) + (1585998703 / 1000000000000000000) + (76239081 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12515 : ℝ) ^ 16 *
      (d.w0 12515 162 + d.w1 12515 162 * √(π / 2) + 2 * d.w2 12515 162 +
        energyR16 12515 * radiusPolynomialRoot16 (d.w0 12515 162) (d.w1 12515 162)
          (d.w2 12515 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12515 : ℝ) ^ 16 *
        (((1915707683 / 100000000000000000000) : ℝ) + ((85186843 / 6250000000000000000)) * (126 / 100) + 2 * ((498002509 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12515) *
          (32 * (((1915707683 / 100000000000000000000) : ℝ) + (85186843 / 6250000000000000000) + (498002509 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12515

/-! A coarse bound on the actual paper statistics constant at dimension 12516. -/
namespace BstLean.Part266.Row12516
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12514 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12514 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12514 128 ≤ (12768 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12768 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12516) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12516 : ℕ))
    (by norm_num : (12516 : ℕ) ≤ 16384)
  have ht : paperTail256 12516 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12516 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12516 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12516 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12516 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12516 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12514 128 * √(2 / (12516 : ℝ)) *
      (√(12516 : ℝ) + paperT0 12516 + paperTail256 12516) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12516 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12516 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12516 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12514 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12514 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12516 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12516

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12516
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12516 (61 / 100) 162 (17 / (100 * 12516)) (26 / (10 * 12516)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12516 (61 / 100) 162 (17 / (100 * 12516)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (497877567 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (795585769 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1438774921 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12516 / 12516 * (61 / 100)) ^ 4 * inverseRadius8 (12516 - 1) /
            envelopeGap 12516 (61 / 100) 162 (17 / (100 * 12516)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12516

namespace BstLean.Part266.Row12516
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12516 162 ≤ (950600833 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12516 162 ≤ (792841281 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (190559671 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12516 162 ≤ (957624549 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12516 162 ≤ (681331539 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12516 162 ≤ (248941571 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (497877567 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (497877567 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (795585769 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1438774921 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3685459 / 1000000000) : ℝ) ≤ √(17 / (100 * 12516) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12516) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1115658513 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19944745787 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12516) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12516) ≤ (22598491 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12516) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12516 * (162 : ℝ) ^ 2 + 26 / (10 * 12516) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12516) : ℝ)) (tA 12516 * 162 ^ 2 + 26 / (10 * 12516)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3685459 / 1000000000))) * ((497877567 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3685459 / 1000000000)) ^ 3) * ((795585769 / 500000000000000000000000))) + ((1438774921 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3685459 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12516) : ℝ)) d.D d.V d.P (√(tA 12516) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3685459 / 1000000000)) ^ 2 * (((1115658513 / 500000000000000)) * ((19944745787 / 500000000000000000)))) + ((1438774921 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12516) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3685459 / 1000000000)) * ((497877567 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12516) : ℝ)) (tA 12516 * 162 ^ 2 + 26 / (10 * 12516)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((497877567 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3685459 / 1000000000)) ^ 2) * ((795585769 / 500000000000000000000000)) + ((1438774921 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12516) : ℝ)) (√(26 / (10 * 12516) : ℝ)) d.D d.V d.P (√(tA 12516) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3685459 / 1000000000)) * (((1115658513 / 500000000000000)) * ((19944745787 / 500000000000000000))) + ((1438774921 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12516) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((497877567 / 100000000000000000000) : ℝ) + ((1438774921 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12516

namespace BstLean.Part266.Row12516
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12516 162 ∧
    0 ≤ (tableEnvelope C).f1 12516 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12516 162 ∧
    0 ≤ (tableEnvelope C).w1 12516 162 ∧ 0 ≤ (tableEnvelope C).w2 12516 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12516 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12516 162 ∧ 0 ≤ d.f1 12516 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12516 162 ∧ 0 ≤ d.w1 12516 162 ∧ 0 ≤ d.w2 12516 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12516 ≤ 2 * (228 / 100 : ℝ) / 12516 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12516 ≤ 2 * (370 / 100 : ℝ) / 12516 := by
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
    (completeRAData (tableEnvelope C) 12516 162).locationBound 12516 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12516 162).energyBound 12516 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12516 162) (d.f1 12516 162) d.f2 ≤
      32 * (((950600833 / 200000000000000000) : ℝ) + (792841281 / 500000000000000000) + (190559671 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12516 162) (d.w1 12516 162)
      (d.w2 12516 162) ≤
      32 * (((957624549 / 50000000000000000000) : ℝ) + (681331539 / 50000000000000000000) + (248941571 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12516 162) (d.f1 12516 162) d.f2 ≤
      ((950600833 / 200000000000000000) : ℝ) ^ 2 + 2 * ((950600833 / 200000000000000000)) * ((792841281 / 500000000000000000)) * (126 / 100) +
      2 * (((792841281 / 500000000000000000)) ^ 2 + 2 * ((950600833 / 200000000000000000)) * ((190559671 / 500000000000000000))) +
      6 * ((792841281 / 500000000000000000)) * ((190559671 / 500000000000000000)) * (126 / 100) + 8 * ((190559671 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12516 162) (d.f1 12516 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12516 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12516 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12516 162) (d.f1 12516 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12516 162) (d.w1 12516 162) (d.w2 12516 162)
  have hwexpr0 : 0 ≤ d.w0 12516 162 + d.w1 12516 162 * √(π / 2) +
      2 * d.w2 12516 162 + energyR16 12516 *
      radiusPolynomialRoot16 (d.w0 12516 162) (d.w1 12516 162) (d.w2 12516 162) := by
    positivity
  constructor
  · change (12516 : ℝ) ^ 8 * (mA 12516 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12516 162) (d.f1 12516 162) d.f2 + locationR16 12516 *
        radiusPolynomialRoot16 (d.f0 12516 162) (d.f1 12516 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12516 : ℝ) ^ 8 * (mA 12516 : ℝ) ^ 8 *
        ((((950600833 / 200000000000000000) : ℝ) ^ 2 + 2 * ((950600833 / 200000000000000000)) * ((792841281 / 500000000000000000)) * (126 / 100) +
          2 * (((792841281 / 500000000000000000)) ^ 2 + 2 * ((950600833 / 200000000000000000)) * ((190559671 / 500000000000000000))) +
          6 * ((792841281 / 500000000000000000)) * ((190559671 / 500000000000000000)) * (126 / 100) + 8 * ((190559671 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12516) *
          (32 * (((950600833 / 200000000000000000) : ℝ) + (792841281 / 500000000000000000) + (190559671 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12516 : ℝ) ^ 16 *
      (d.w0 12516 162 + d.w1 12516 162 * √(π / 2) + 2 * d.w2 12516 162 +
        energyR16 12516 * radiusPolynomialRoot16 (d.w0 12516 162) (d.w1 12516 162)
          (d.w2 12516 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12516 : ℝ) ^ 16 *
        (((957624549 / 50000000000000000000) : ℝ) + ((681331539 / 50000000000000000000)) * (126 / 100) + 2 * ((248941571 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12516) *
          (32 * (((957624549 / 50000000000000000000) : ℝ) + (681331539 / 50000000000000000000) + (248941571 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12516

/-! A coarse bound on the actual paper statistics constant at dimension 12517. -/
namespace BstLean.Part266.Row12517
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12515 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12515 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12515 128 ≤ (12769 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12769 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12517) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12517 : ℕ))
    (by norm_num : (12517 : ℕ) ≤ 16384)
  have ht : paperTail256 12517 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12517 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12517 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12517 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12517 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12517 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12515 128 * √(2 / (12517 : ℝ)) *
      (√(12517 : ℝ) + paperT0 12517 + paperTail256 12517) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12517 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12517 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12517 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12515 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12515 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12517 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12517

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12517
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12517 (61 / 100) 162 (17 / (100 * 12517)) (26 / (10 * 12517)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12517 (61 / 100) 162 (17 / (100 * 12517)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (248879121 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (198832887 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1150277207 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12517 / 12517 * (61 / 100)) ^ 4 * inverseRadius8 (12517 - 1) /
            envelopeGap 12517 (61 / 100) 162 (17 / (100 * 12517)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12517

namespace BstLean.Part266.Row12517
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12517 162 ≤ (475205403 / 100000000000000000)
  f1 : (tableEnvelope C).f1 12517 162 ≤ (792682833 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (381043199 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12517 162 ≤ (382957981 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12517 162 ≤ (1362336411 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12517 162 ≤ (248881907 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (248879121 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (248879121 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (198832887 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1150277207 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((57583 / 15625000) : ℝ) ≤ √(17 / (100 * 12517) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12517) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2231049623 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39883117933 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12517) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12517) ≤ (28245857 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12517) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12517 * (162 : ℝ) ^ 2 + 26 / (10 * 12517) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12517) : ℝ)) (tA 12517 * 162 ^ 2 + 26 / (10 * 12517)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((57583 / 15625000))) * ((248879121 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((57583 / 15625000)) ^ 3) * ((198832887 / 125000000000000000000000))) + ((1150277207 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((57583 / 15625000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12517) : ℝ)) d.D d.V d.P (√(tA 12517) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((57583 / 15625000)) ^ 2 * (((2231049623 / 1000000000000000)) * ((39883117933 / 1000000000000000000)))) + ((1150277207 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12517) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((57583 / 15625000)) * ((248879121 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12517) : ℝ)) (tA 12517 * 162 ^ 2 + 26 / (10 * 12517)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((248879121 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((57583 / 15625000)) ^ 2) * ((198832887 / 125000000000000000000000)) + ((1150277207 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12517) : ℝ)) (√(26 / (10 * 12517) : ℝ)) d.D d.V d.P (√(tA 12517) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((57583 / 15625000)) * (((2231049623 / 1000000000000000)) * ((39883117933 / 1000000000000000000))) + ((1150277207 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12517) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((248879121 / 50000000000000000000) : ℝ) + ((1150277207 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12517

namespace BstLean.Part266.Row12517
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12517 162 ∧
    0 ≤ (tableEnvelope C).f1 12517 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12517 162 ∧
    0 ≤ (tableEnvelope C).w1 12517 162 ∧ 0 ≤ (tableEnvelope C).w2 12517 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12517 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12517 162 ∧ 0 ≤ d.f1 12517 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12517 162 ∧ 0 ≤ d.w1 12517 162 ∧ 0 ≤ d.w2 12517 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12517 ≤ 2 * (228 / 100 : ℝ) / 12517 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12517 ≤ 2 * (370 / 100 : ℝ) / 12517 := by
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
    (completeRAData (tableEnvelope C) 12517 162).locationBound 12517 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12517 162).energyBound 12517 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12517 162) (d.f1 12517 162) d.f2 ≤
      32 * (((475205403 / 100000000000000000) : ℝ) + (792682833 / 500000000000000000) + (381043199 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12517 162) (d.w1 12517 162)
      (d.w2 12517 162) ≤
      32 * (((382957981 / 20000000000000000000) : ℝ) + (1362336411 / 100000000000000000000) + (248881907 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12517 162) (d.f1 12517 162) d.f2 ≤
      ((475205403 / 100000000000000000) : ℝ) ^ 2 + 2 * ((475205403 / 100000000000000000)) * ((792682833 / 500000000000000000)) * (126 / 100) +
      2 * (((792682833 / 500000000000000000)) ^ 2 + 2 * ((475205403 / 100000000000000000)) * ((381043199 / 1000000000000000000))) +
      6 * ((792682833 / 500000000000000000)) * ((381043199 / 1000000000000000000)) * (126 / 100) + 8 * ((381043199 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12517 162) (d.f1 12517 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12517 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12517 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12517 162) (d.f1 12517 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12517 162) (d.w1 12517 162) (d.w2 12517 162)
  have hwexpr0 : 0 ≤ d.w0 12517 162 + d.w1 12517 162 * √(π / 2) +
      2 * d.w2 12517 162 + energyR16 12517 *
      radiusPolynomialRoot16 (d.w0 12517 162) (d.w1 12517 162) (d.w2 12517 162) := by
    positivity
  constructor
  · change (12517 : ℝ) ^ 8 * (mA 12517 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12517 162) (d.f1 12517 162) d.f2 + locationR16 12517 *
        radiusPolynomialRoot16 (d.f0 12517 162) (d.f1 12517 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12517 : ℝ) ^ 8 * (mA 12517 : ℝ) ^ 8 *
        ((((475205403 / 100000000000000000) : ℝ) ^ 2 + 2 * ((475205403 / 100000000000000000)) * ((792682833 / 500000000000000000)) * (126 / 100) +
          2 * (((792682833 / 500000000000000000)) ^ 2 + 2 * ((475205403 / 100000000000000000)) * ((381043199 / 1000000000000000000))) +
          6 * ((792682833 / 500000000000000000)) * ((381043199 / 1000000000000000000)) * (126 / 100) + 8 * ((381043199 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12517) *
          (32 * (((475205403 / 100000000000000000) : ℝ) + (792682833 / 500000000000000000) + (381043199 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12517 : ℝ) ^ 16 *
      (d.w0 12517 162 + d.w1 12517 162 * √(π / 2) + 2 * d.w2 12517 162 +
        energyR16 12517 * radiusPolynomialRoot16 (d.w0 12517 162) (d.w1 12517 162)
          (d.w2 12517 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12517 : ℝ) ^ 16 *
        (((382957981 / 20000000000000000000) : ℝ) + ((1362336411 / 100000000000000000000)) * (126 / 100) + 2 * ((248881907 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12517) *
          (32 * (((382957981 / 20000000000000000000) : ℝ) + (1362336411 / 100000000000000000000) + (248881907 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12517

/-! A coarse bound on the actual paper statistics constant at dimension 12518. -/
namespace BstLean.Part266.Row12518
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12516 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12516 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12516 128 ≤ (12770 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12770 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12518) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12518 : ℕ))
    (by norm_num : (12518 : ℕ) ≤ 16384)
  have ht : paperTail256 12518 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12518 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12518 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12518 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12518 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12518 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12516 128 * √(2 / (12518 : ℝ)) *
      (√(12518 : ℝ) + paperT0 12518 + paperTail256 12518) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12518 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12518 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12518 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12516 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12516 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12518 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12518

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12518
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12518 (61 / 100) 162 (17 / (100 * 12518)) (26 / (10 * 12518)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12518 (61 / 100) 162 (17 / (100 * 12518)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (99527791 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (198769357 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1149535017 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12518 / 12518 * (61 / 100)) ^ 4 * inverseRadius8 (12518 - 1) /
            envelopeGap 12518 (61 / 100) 162 (17 / (100 * 12518)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12518

namespace BstLean.Part266.Row12518
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12518 162 ≤ (148472007 / 31250000000000000)
  f1 : (tableEnvelope C).f1 12518 162 ≤ (198131109 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (190483539 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12518 162 ≤ (1914330871 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12518 162 ≤ (681004927 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12518 162 ≤ (497644523 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (99527791 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (99527791 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (198769357 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1149535017 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((737033 / 200000000) : ℝ) ≤ √(17 / (100 * 12518) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12518) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1115391137 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19938372903 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12518) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12518) ≤ (56487201 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12518) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12518 * (162 : ℝ) ^ 2 + 26 / (10 * 12518) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12518) : ℝ)) (tA 12518 * 162 ^ 2 + 26 / (10 * 12518)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((737033 / 200000000))) * ((99527791 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((737033 / 200000000)) ^ 3) * ((198769357 / 125000000000000000000000))) + ((1149535017 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((737033 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12518) : ℝ)) d.D d.V d.P (√(tA 12518) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((737033 / 200000000)) ^ 2 * (((1115391137 / 500000000000000)) * ((19938372903 / 500000000000000000)))) + ((1149535017 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12518) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((737033 / 200000000)) * ((99527791 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12518) : ℝ)) (tA 12518 * 162 ^ 2 + 26 / (10 * 12518)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((99527791 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((737033 / 200000000)) ^ 2) * ((198769357 / 125000000000000000000000)) + ((1149535017 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12518) : ℝ)) (√(26 / (10 * 12518) : ℝ)) d.D d.V d.P (√(tA 12518) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((737033 / 200000000)) * (((1115391137 / 500000000000000)) * ((19938372903 / 500000000000000000))) + ((1149535017 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12518) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((99527791 / 20000000000000000000) : ℝ) + ((1149535017 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12518

namespace BstLean.Part266.Row12518
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12518 162 ∧
    0 ≤ (tableEnvelope C).f1 12518 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12518 162 ∧
    0 ≤ (tableEnvelope C).w1 12518 162 ∧ 0 ≤ (tableEnvelope C).w2 12518 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12518 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12518 162 ∧ 0 ≤ d.f1 12518 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12518 162 ∧ 0 ≤ d.w1 12518 162 ∧ 0 ≤ d.w2 12518 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12518 ≤ 2 * (228 / 100 : ℝ) / 12518 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12518 ≤ 2 * (370 / 100 : ℝ) / 12518 := by
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
    (completeRAData (tableEnvelope C) 12518 162).locationBound 12518 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12518 162).energyBound 12518 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12518 162) (d.f1 12518 162) d.f2 ≤
      32 * (((148472007 / 31250000000000000) : ℝ) + (198131109 / 125000000000000000) + (190483539 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12518 162) (d.w1 12518 162)
      (d.w2 12518 162) ≤
      32 * (((1914330871 / 100000000000000000000) : ℝ) + (681004927 / 50000000000000000000) + (497644523 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12518 162) (d.f1 12518 162) d.f2 ≤
      ((148472007 / 31250000000000000) : ℝ) ^ 2 + 2 * ((148472007 / 31250000000000000)) * ((198131109 / 125000000000000000)) * (126 / 100) +
      2 * (((198131109 / 125000000000000000)) ^ 2 + 2 * ((148472007 / 31250000000000000)) * ((190483539 / 500000000000000000))) +
      6 * ((198131109 / 125000000000000000)) * ((190483539 / 500000000000000000)) * (126 / 100) + 8 * ((190483539 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12518 162) (d.f1 12518 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12518 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12518 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12518 162) (d.f1 12518 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12518 162) (d.w1 12518 162) (d.w2 12518 162)
  have hwexpr0 : 0 ≤ d.w0 12518 162 + d.w1 12518 162 * √(π / 2) +
      2 * d.w2 12518 162 + energyR16 12518 *
      radiusPolynomialRoot16 (d.w0 12518 162) (d.w1 12518 162) (d.w2 12518 162) := by
    positivity
  constructor
  · change (12518 : ℝ) ^ 8 * (mA 12518 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12518 162) (d.f1 12518 162) d.f2 + locationR16 12518 *
        radiusPolynomialRoot16 (d.f0 12518 162) (d.f1 12518 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12518 : ℝ) ^ 8 * (mA 12518 : ℝ) ^ 8 *
        ((((148472007 / 31250000000000000) : ℝ) ^ 2 + 2 * ((148472007 / 31250000000000000)) * ((198131109 / 125000000000000000)) * (126 / 100) +
          2 * (((198131109 / 125000000000000000)) ^ 2 + 2 * ((148472007 / 31250000000000000)) * ((190483539 / 500000000000000000))) +
          6 * ((198131109 / 125000000000000000)) * ((190483539 / 500000000000000000)) * (126 / 100) + 8 * ((190483539 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12518) *
          (32 * (((148472007 / 31250000000000000) : ℝ) + (198131109 / 125000000000000000) + (190483539 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12518 : ℝ) ^ 16 *
      (d.w0 12518 162 + d.w1 12518 162 * √(π / 2) + 2 * d.w2 12518 162 +
        energyR16 12518 * radiusPolynomialRoot16 (d.w0 12518 162) (d.w1 12518 162)
          (d.w2 12518 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12518 : ℝ) ^ 16 *
        (((1914330871 / 100000000000000000000) : ℝ) + ((681004927 / 50000000000000000000)) * (126 / 100) + 2 * ((497644523 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12518) *
          (32 * (((1914330871 / 100000000000000000000) : ℝ) + (681004927 / 50000000000000000000) + (497644523 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12518

/-! A coarse bound on the actual paper statistics constant at dimension 12519. -/
namespace BstLean.Part266.Row12519
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12517 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12517 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12517 128 ≤ (12771 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12771 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12519) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12519 : ℕ))
    (by norm_num : (12519 : ℕ) ≤ 16384)
  have ht : paperTail256 12519 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12519 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12519 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12519 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12519 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12519 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12517 128 * √(2 / (12519 : ℝ)) *
      (√(12519 : ℝ) + paperT0 12519 + paperTail256 12519) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12519 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12519 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12519 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12517 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12517 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12519 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12519

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12519
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12519 (61 / 100) 162 (17 / (100 * 12519)) (26 / (10 * 12519)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12519 (61 / 100) 162 (17 / (100 * 12519)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (248759853 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1589646819 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5743966831 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12519 / 12519 * (61 / 100)) ^ 4 * inverseRadius8 (12519 - 1) /
            envelopeGap 12519 (61 / 100) 162 (17 / (100 * 12519)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12519

namespace BstLean.Part266.Row12519
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12519 162 ≤ (4750154749 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12519 162 ≤ (792366091 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (380890981 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12519 162 ≤ (956935999 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12519 162 ≤ (1361683407 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12519 162 ≤ (497525271 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (248759853 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (248759853 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1589646819 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5743966831 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1842509 / 500000000) : ℝ) ≤ √(17 / (100 * 12519) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12519) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2230514977 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19935187603 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12519) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12519) ≤ (56482689 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12519) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12519 * (162 : ℝ) ^ 2 + 26 / (10 * 12519) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12519) : ℝ)) (tA 12519 * 162 ^ 2 + 26 / (10 * 12519)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1842509 / 500000000))) * ((248759853 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1842509 / 500000000)) ^ 3) * ((1589646819 / 1000000000000000000000000))) + ((5743966831 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1842509 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12519) : ℝ)) d.D d.V d.P (√(tA 12519) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1842509 / 500000000)) ^ 2 * (((2230514977 / 1000000000000000)) * ((19935187603 / 500000000000000000)))) + ((5743966831 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12519) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1842509 / 500000000)) * ((248759853 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12519) : ℝ)) (tA 12519 * 162 ^ 2 + 26 / (10 * 12519)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((248759853 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1842509 / 500000000)) ^ 2) * ((1589646819 / 1000000000000000000000000)) + ((5743966831 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12519) : ℝ)) (√(26 / (10 * 12519) : ℝ)) d.D d.V d.P (√(tA 12519) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1842509 / 500000000)) * (((2230514977 / 1000000000000000)) * ((19935187603 / 500000000000000000))) + ((5743966831 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12519) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((248759853 / 50000000000000000000) : ℝ) + ((5743966831 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12519

namespace BstLean.Part266.Row12519
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12519 162 ∧
    0 ≤ (tableEnvelope C).f1 12519 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12519 162 ∧
    0 ≤ (tableEnvelope C).w1 12519 162 ∧ 0 ≤ (tableEnvelope C).w2 12519 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12519 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12519 162 ∧ 0 ≤ d.f1 12519 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12519 162 ∧ 0 ≤ d.w1 12519 162 ∧ 0 ≤ d.w2 12519 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12519 ≤ 2 * (228 / 100 : ℝ) / 12519 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12519 ≤ 2 * (370 / 100 : ℝ) / 12519 := by
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
    (completeRAData (tableEnvelope C) 12519 162).locationBound 12519 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12519 162).energyBound 12519 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12519 162) (d.f1 12519 162) d.f2 ≤
      32 * (((4750154749 / 1000000000000000000) : ℝ) + (792366091 / 500000000000000000) + (380890981 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12519 162) (d.w1 12519 162)
      (d.w2 12519 162) ≤
      32 * (((956935999 / 50000000000000000000) : ℝ) + (1361683407 / 100000000000000000000) + (497525271 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12519 162) (d.f1 12519 162) d.f2 ≤
      ((4750154749 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4750154749 / 1000000000000000000)) * ((792366091 / 500000000000000000)) * (126 / 100) +
      2 * (((792366091 / 500000000000000000)) ^ 2 + 2 * ((4750154749 / 1000000000000000000)) * ((380890981 / 1000000000000000000))) +
      6 * ((792366091 / 500000000000000000)) * ((380890981 / 1000000000000000000)) * (126 / 100) + 8 * ((380890981 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12519 162) (d.f1 12519 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12519 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12519 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12519 162) (d.f1 12519 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12519 162) (d.w1 12519 162) (d.w2 12519 162)
  have hwexpr0 : 0 ≤ d.w0 12519 162 + d.w1 12519 162 * √(π / 2) +
      2 * d.w2 12519 162 + energyR16 12519 *
      radiusPolynomialRoot16 (d.w0 12519 162) (d.w1 12519 162) (d.w2 12519 162) := by
    positivity
  constructor
  · change (12519 : ℝ) ^ 8 * (mA 12519 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12519 162) (d.f1 12519 162) d.f2 + locationR16 12519 *
        radiusPolynomialRoot16 (d.f0 12519 162) (d.f1 12519 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12519 : ℝ) ^ 8 * (mA 12519 : ℝ) ^ 8 *
        ((((4750154749 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4750154749 / 1000000000000000000)) * ((792366091 / 500000000000000000)) * (126 / 100) +
          2 * (((792366091 / 500000000000000000)) ^ 2 + 2 * ((4750154749 / 1000000000000000000)) * ((380890981 / 1000000000000000000))) +
          6 * ((792366091 / 500000000000000000)) * ((380890981 / 1000000000000000000)) * (126 / 100) + 8 * ((380890981 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12519) *
          (32 * (((4750154749 / 1000000000000000000) : ℝ) + (792366091 / 500000000000000000) + (380890981 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12519 : ℝ) ^ 16 *
      (d.w0 12519 162 + d.w1 12519 162 * √(π / 2) + 2 * d.w2 12519 162 +
        energyR16 12519 * radiusPolynomialRoot16 (d.w0 12519 162) (d.w1 12519 162)
          (d.w2 12519 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12519 : ℝ) ^ 16 *
        (((956935999 / 50000000000000000000) : ℝ) + ((1361683407 / 100000000000000000000)) * (126 / 100) + 2 * ((497525271 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12519) *
          (32 * (((956935999 / 50000000000000000000) : ℝ) + (1361683407 / 100000000000000000000) + (497525271 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12519

/-! A coarse bound on the actual paper statistics constant at dimension 12520. -/
namespace BstLean.Part266.Row12520
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12518 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12518 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12518 128 ≤ (12772 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12772 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12520) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12520 : ℕ))
    (by norm_num : (12520 : ℕ) ≤ 16384)
  have ht : paperTail256 12520 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12520 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12520 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12520 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12520 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12520 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12518 128 * √(2 / (12520 : ℝ)) *
      (√(12520 : ℝ) + paperT0 12520 + paperTail256 12520) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12520 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12520 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12520 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12518 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12518 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12520 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12520

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12520
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12520 (61 / 100) 162 (17 / (100 * 12520)) (26 / (10 * 12520)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12520 (61 / 100) 162 (17 / (100 * 12520)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (99480099 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (317827797 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (717532659 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12520 / 12520 * (61 / 100)) ^ 4 * inverseRadius8 (12520 - 1) /
            envelopeGap 12520 (61 / 100) 162 (17 / (100 * 12520)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12520

namespace BstLean.Part266.Row12520
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12520 162 ≤ (949841121 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12520 162 ≤ (316883119 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (380814907 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12520 162 ≤ (478353321 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12520 162 ≤ (136135707 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 12520 162 ≤ (62175757 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (99480099 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (99480099 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (317827797 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (717532659 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3684871 / 1000000000) : ℝ) ≤ √(17 / (100 * 12520) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12520) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2230247733 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19932003067 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12520) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12520) ≤ (22591271 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12520) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12520 * (162 : ℝ) ^ 2 + 26 / (10 * 12520) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12520) : ℝ)) (tA 12520 * 162 ^ 2 + 26 / (10 * 12520)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3684871 / 1000000000))) * ((99480099 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3684871 / 1000000000)) ^ 3) * ((317827797 / 200000000000000000000000))) + ((717532659 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3684871 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12520) : ℝ)) d.D d.V d.P (√(tA 12520) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3684871 / 1000000000)) ^ 2 * (((2230247733 / 1000000000000000)) * ((19932003067 / 500000000000000000)))) + ((717532659 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12520) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3684871 / 1000000000)) * ((99480099 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12520) : ℝ)) (tA 12520 * 162 ^ 2 + 26 / (10 * 12520)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((99480099 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3684871 / 1000000000)) ^ 2) * ((317827797 / 200000000000000000000000)) + ((717532659 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12520) : ℝ)) (√(26 / (10 * 12520) : ℝ)) d.D d.V d.P (√(tA 12520) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3684871 / 1000000000)) * (((2230247733 / 1000000000000000)) * ((19932003067 / 500000000000000000))) + ((717532659 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12520) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((99480099 / 20000000000000000000) : ℝ) + ((717532659 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12520

namespace BstLean.Part266.Row12520
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12520 162 ∧
    0 ≤ (tableEnvelope C).f1 12520 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12520 162 ∧
    0 ≤ (tableEnvelope C).w1 12520 162 ∧ 0 ≤ (tableEnvelope C).w2 12520 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12520 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12520 162 ∧ 0 ≤ d.f1 12520 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12520 162 ∧ 0 ≤ d.w1 12520 162 ∧ 0 ≤ d.w2 12520 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12520 ≤ 2 * (228 / 100 : ℝ) / 12520 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12520 ≤ 2 * (370 / 100 : ℝ) / 12520 := by
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
    (completeRAData (tableEnvelope C) 12520 162).locationBound 12520 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12520 162).energyBound 12520 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12520 162) (d.f1 12520 162) d.f2 ≤
      32 * (((949841121 / 200000000000000000) : ℝ) + (316883119 / 200000000000000000) + (380814907 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12520 162) (d.w1 12520 162)
      (d.w2 12520 162) ≤
      32 * (((478353321 / 25000000000000000000) : ℝ) + (136135707 / 10000000000000000000) + (62175757 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12520 162) (d.f1 12520 162) d.f2 ≤
      ((949841121 / 200000000000000000) : ℝ) ^ 2 + 2 * ((949841121 / 200000000000000000)) * ((316883119 / 200000000000000000)) * (126 / 100) +
      2 * (((316883119 / 200000000000000000)) ^ 2 + 2 * ((949841121 / 200000000000000000)) * ((380814907 / 1000000000000000000))) +
      6 * ((316883119 / 200000000000000000)) * ((380814907 / 1000000000000000000)) * (126 / 100) + 8 * ((380814907 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12520 162) (d.f1 12520 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12520 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12520 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12520 162) (d.f1 12520 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12520 162) (d.w1 12520 162) (d.w2 12520 162)
  have hwexpr0 : 0 ≤ d.w0 12520 162 + d.w1 12520 162 * √(π / 2) +
      2 * d.w2 12520 162 + energyR16 12520 *
      radiusPolynomialRoot16 (d.w0 12520 162) (d.w1 12520 162) (d.w2 12520 162) := by
    positivity
  constructor
  · change (12520 : ℝ) ^ 8 * (mA 12520 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12520 162) (d.f1 12520 162) d.f2 + locationR16 12520 *
        radiusPolynomialRoot16 (d.f0 12520 162) (d.f1 12520 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12520 : ℝ) ^ 8 * (mA 12520 : ℝ) ^ 8 *
        ((((949841121 / 200000000000000000) : ℝ) ^ 2 + 2 * ((949841121 / 200000000000000000)) * ((316883119 / 200000000000000000)) * (126 / 100) +
          2 * (((316883119 / 200000000000000000)) ^ 2 + 2 * ((949841121 / 200000000000000000)) * ((380814907 / 1000000000000000000))) +
          6 * ((316883119 / 200000000000000000)) * ((380814907 / 1000000000000000000)) * (126 / 100) + 8 * ((380814907 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12520) *
          (32 * (((949841121 / 200000000000000000) : ℝ) + (316883119 / 200000000000000000) + (380814907 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12520 : ℝ) ^ 16 *
      (d.w0 12520 162 + d.w1 12520 162 * √(π / 2) + 2 * d.w2 12520 162 +
        energyR16 12520 * radiusPolynomialRoot16 (d.w0 12520 162) (d.w1 12520 162)
          (d.w2 12520 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12520 : ℝ) ^ 16 *
        (((478353321 / 25000000000000000000) : ℝ) + ((136135707 / 10000000000000000000)) * (126 / 100) + 2 * ((62175757 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12520) *
          (32 * (((478353321 / 25000000000000000000) : ℝ) + (136135707 / 10000000000000000000) + (62175757 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12520

/-! A coarse bound on the actual paper statistics constant at dimension 12521. -/
namespace BstLean.Part266.Row12521
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12519 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12519 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12519 128 ≤ (12773 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12773 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12521) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12521 : ℕ))
    (by norm_num : (12521 : ℕ) ≤ 16384)
  have ht : paperTail256 12521 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12521 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12521 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12521 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12521 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12521 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12519 128 * √(2 / (12521 : ℝ)) *
      (√(12521 : ℝ) + paperT0 12521 + paperTail256 12521) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12521 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12521 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12521 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12519 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12519 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12521 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12521

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12521
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12521 (61 / 100) 162 (17 / (100 * 12521)) (26 / (10 * 12521)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12521 (61 / 100) 162 (17 / (100 * 12521)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (248640661 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (794315677 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1434139601 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12521 / 12521 * (61 / 100)) ^ 4 * inverseRadius8 (12521 - 1) /
            envelopeGap 12521 (61 / 100) 162 (17 / (100 * 12521)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12521

namespace BstLean.Part266.Row12521
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12521 162 ≤ (4748260513 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12521 162 ≤ (396024993 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (380738959 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12521 162 ≤ (1912955499 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12521 162 ≤ (680515607 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12521 162 ≤ (497286879 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (248640661 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (248640661 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (794315677 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1434139601 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3684723 / 1000000000) : ℝ) ≤ √(17 / (100 * 12521) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12521) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2229980543 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39857638591 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12521) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12521) ≤ (56473667 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12521) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12521 * (162 : ℝ) ^ 2 + 26 / (10 * 12521) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12521) : ℝ)) (tA 12521 * 162 ^ 2 + 26 / (10 * 12521)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3684723 / 1000000000))) * ((248640661 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3684723 / 1000000000)) ^ 3) * ((794315677 / 500000000000000000000000))) + ((1434139601 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3684723 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12521) : ℝ)) d.D d.V d.P (√(tA 12521) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3684723 / 1000000000)) ^ 2 * (((2229980543 / 1000000000000000)) * ((39857638591 / 1000000000000000000)))) + ((1434139601 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12521) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3684723 / 1000000000)) * ((248640661 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12521) : ℝ)) (tA 12521 * 162 ^ 2 + 26 / (10 * 12521)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((248640661 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3684723 / 1000000000)) ^ 2) * ((794315677 / 500000000000000000000000)) + ((1434139601 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12521) : ℝ)) (√(26 / (10 * 12521) : ℝ)) d.D d.V d.P (√(tA 12521) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3684723 / 1000000000)) * (((2229980543 / 1000000000000000)) * ((39857638591 / 1000000000000000000))) + ((1434139601 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12521) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((248640661 / 50000000000000000000) : ℝ) + ((1434139601 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12521

namespace BstLean.Part266.Row12521
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12521 162 ∧
    0 ≤ (tableEnvelope C).f1 12521 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12521 162 ∧
    0 ≤ (tableEnvelope C).w1 12521 162 ∧ 0 ≤ (tableEnvelope C).w2 12521 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12521 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12521 162 ∧ 0 ≤ d.f1 12521 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12521 162 ∧ 0 ≤ d.w1 12521 162 ∧ 0 ≤ d.w2 12521 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12521 ≤ 2 * (228 / 100 : ℝ) / 12521 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12521 ≤ 2 * (370 / 100 : ℝ) / 12521 := by
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
    (completeRAData (tableEnvelope C) 12521 162).locationBound 12521 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12521 162).energyBound 12521 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12521 162) (d.f1 12521 162) d.f2 ≤
      32 * (((4748260513 / 1000000000000000000) : ℝ) + (396024993 / 250000000000000000) + (380738959 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12521 162) (d.w1 12521 162)
      (d.w2 12521 162) ≤
      32 * (((1912955499 / 100000000000000000000) : ℝ) + (680515607 / 50000000000000000000) + (497286879 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12521 162) (d.f1 12521 162) d.f2 ≤
      ((4748260513 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4748260513 / 1000000000000000000)) * ((396024993 / 250000000000000000)) * (126 / 100) +
      2 * (((396024993 / 250000000000000000)) ^ 2 + 2 * ((4748260513 / 1000000000000000000)) * ((380738959 / 1000000000000000000))) +
      6 * ((396024993 / 250000000000000000)) * ((380738959 / 1000000000000000000)) * (126 / 100) + 8 * ((380738959 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12521 162) (d.f1 12521 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12521 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12521 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12521 162) (d.f1 12521 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12521 162) (d.w1 12521 162) (d.w2 12521 162)
  have hwexpr0 : 0 ≤ d.w0 12521 162 + d.w1 12521 162 * √(π / 2) +
      2 * d.w2 12521 162 + energyR16 12521 *
      radiusPolynomialRoot16 (d.w0 12521 162) (d.w1 12521 162) (d.w2 12521 162) := by
    positivity
  constructor
  · change (12521 : ℝ) ^ 8 * (mA 12521 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12521 162) (d.f1 12521 162) d.f2 + locationR16 12521 *
        radiusPolynomialRoot16 (d.f0 12521 162) (d.f1 12521 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12521 : ℝ) ^ 8 * (mA 12521 : ℝ) ^ 8 *
        ((((4748260513 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4748260513 / 1000000000000000000)) * ((396024993 / 250000000000000000)) * (126 / 100) +
          2 * (((396024993 / 250000000000000000)) ^ 2 + 2 * ((4748260513 / 1000000000000000000)) * ((380738959 / 1000000000000000000))) +
          6 * ((396024993 / 250000000000000000)) * ((380738959 / 1000000000000000000)) * (126 / 100) + 8 * ((380738959 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12521) *
          (32 * (((4748260513 / 1000000000000000000) : ℝ) + (396024993 / 250000000000000000) + (380738959 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12521 : ℝ) ^ 16 *
      (d.w0 12521 162 + d.w1 12521 162 * √(π / 2) + 2 * d.w2 12521 162 +
        energyR16 12521 * radiusPolynomialRoot16 (d.w0 12521 162) (d.w1 12521 162)
          (d.w2 12521 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12521 : ℝ) ^ 16 *
        (((1912955499 / 100000000000000000000) : ℝ) + ((680515607 / 50000000000000000000)) * (126 / 100) + 2 * ((497286879 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12521) *
          (32 * (((1912955499 / 100000000000000000000) : ℝ) + (680515607 / 50000000000000000000) + (497286879 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12521

/-! A coarse bound on the actual paper statistics constant at dimension 12522. -/
namespace BstLean.Part266.Row12522
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12520 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12520 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12520 128 ≤ (12774 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12774 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12522) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12522 : ℕ))
    (by norm_num : (12522 : ℕ) ≤ 16384)
  have ht : paperTail256 12522 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12522 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12522 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12522 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12522 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12522 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12520 128 * √(2 / (12522 : ℝ)) *
      (√(12522 : ℝ) + paperT0 12522 + paperTail256 12522) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12522 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12522 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12522 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12520 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12520 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12522 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12522

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12522
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12522 (61 / 100) 162 (17 / (100 * 12522)) (26 / (10 * 12522)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12522 (61 / 100) 162 (17 / (100 * 12522)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (124290547 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (794061963 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2866429113 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12522 / 12522 * (61 / 100)) ^ 4 * inverseRadius8 (12522 - 1) /
            envelopeGap 12522 (61 / 100) 162 (17 / (100 * 12522)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12522

namespace BstLean.Part266.Row12522
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12522 162 ≤ (148353501 / 31250000000000000)
  f1 : (tableEnvelope C).f1 12522 162 ≤ (791891797 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (380662931 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12522 162 ≤ (1912497107 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12522 162 ≤ (1360705101 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12522 162 ≤ (248583871 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (124290547 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (124290547 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (794061963 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2866429113 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((115143 / 31250000) : ℝ) ≤ √(17 / (100 * 12522) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12522) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (4354909 / 1953125000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39851272577 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12522) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12522) ≤ (56469157 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12522) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12522 * (162 : ℝ) ^ 2 + 26 / (10 * 12522) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12522) : ℝ)) (tA 12522 * 162 ^ 2 + 26 / (10 * 12522)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((115143 / 31250000))) * ((124290547 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((115143 / 31250000)) ^ 3) * ((794061963 / 500000000000000000000000))) + ((2866429113 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((115143 / 31250000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12522) : ℝ)) d.D d.V d.P (√(tA 12522) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((115143 / 31250000)) ^ 2 * (((4354909 / 1953125000000)) * ((39851272577 / 1000000000000000000)))) + ((2866429113 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12522) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((115143 / 31250000)) * ((124290547 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12522) : ℝ)) (tA 12522 * 162 ^ 2 + 26 / (10 * 12522)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((124290547 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((115143 / 31250000)) ^ 2) * ((794061963 / 500000000000000000000000)) + ((2866429113 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12522) : ℝ)) (√(26 / (10 * 12522) : ℝ)) d.D d.V d.P (√(tA 12522) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((115143 / 31250000)) * (((4354909 / 1953125000000)) * ((39851272577 / 1000000000000000000))) + ((2866429113 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12522) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((124290547 / 25000000000000000000) : ℝ) + ((2866429113 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12522

namespace BstLean.Part266.Row12522
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12522 162 ∧
    0 ≤ (tableEnvelope C).f1 12522 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12522 162 ∧
    0 ≤ (tableEnvelope C).w1 12522 162 ∧ 0 ≤ (tableEnvelope C).w2 12522 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12522 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12522 162 ∧ 0 ≤ d.f1 12522 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12522 162 ∧ 0 ≤ d.w1 12522 162 ∧ 0 ≤ d.w2 12522 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12522 ≤ 2 * (228 / 100 : ℝ) / 12522 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12522 ≤ 2 * (370 / 100 : ℝ) / 12522 := by
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
    (completeRAData (tableEnvelope C) 12522 162).locationBound 12522 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12522 162).energyBound 12522 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12522 162) (d.f1 12522 162) d.f2 ≤
      32 * (((148353501 / 31250000000000000) : ℝ) + (791891797 / 500000000000000000) + (380662931 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12522 162) (d.w1 12522 162)
      (d.w2 12522 162) ≤
      32 * (((1912497107 / 100000000000000000000) : ℝ) + (1360705101 / 100000000000000000000) + (248583871 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12522 162) (d.f1 12522 162) d.f2 ≤
      ((148353501 / 31250000000000000) : ℝ) ^ 2 + 2 * ((148353501 / 31250000000000000)) * ((791891797 / 500000000000000000)) * (126 / 100) +
      2 * (((791891797 / 500000000000000000)) ^ 2 + 2 * ((148353501 / 31250000000000000)) * ((380662931 / 1000000000000000000))) +
      6 * ((791891797 / 500000000000000000)) * ((380662931 / 1000000000000000000)) * (126 / 100) + 8 * ((380662931 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12522 162) (d.f1 12522 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12522 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12522 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12522 162) (d.f1 12522 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12522 162) (d.w1 12522 162) (d.w2 12522 162)
  have hwexpr0 : 0 ≤ d.w0 12522 162 + d.w1 12522 162 * √(π / 2) +
      2 * d.w2 12522 162 + energyR16 12522 *
      radiusPolynomialRoot16 (d.w0 12522 162) (d.w1 12522 162) (d.w2 12522 162) := by
    positivity
  constructor
  · change (12522 : ℝ) ^ 8 * (mA 12522 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12522 162) (d.f1 12522 162) d.f2 + locationR16 12522 *
        radiusPolynomialRoot16 (d.f0 12522 162) (d.f1 12522 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12522 : ℝ) ^ 8 * (mA 12522 : ℝ) ^ 8 *
        ((((148353501 / 31250000000000000) : ℝ) ^ 2 + 2 * ((148353501 / 31250000000000000)) * ((791891797 / 500000000000000000)) * (126 / 100) +
          2 * (((791891797 / 500000000000000000)) ^ 2 + 2 * ((148353501 / 31250000000000000)) * ((380662931 / 1000000000000000000))) +
          6 * ((791891797 / 500000000000000000)) * ((380662931 / 1000000000000000000)) * (126 / 100) + 8 * ((380662931 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12522) *
          (32 * (((148353501 / 31250000000000000) : ℝ) + (791891797 / 500000000000000000) + (380662931 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12522 : ℝ) ^ 16 *
      (d.w0 12522 162 + d.w1 12522 162 * √(π / 2) + 2 * d.w2 12522 162 +
        energyR16 12522 * radiusPolynomialRoot16 (d.w0 12522 162) (d.w1 12522 162)
          (d.w2 12522 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12522 : ℝ) ^ 16 *
        (((1912497107 / 100000000000000000000) : ℝ) + ((1360705101 / 100000000000000000000)) * (126 / 100) + 2 * ((248583871 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12522) *
          (32 * (((1912497107 / 100000000000000000000) : ℝ) + (1360705101 / 100000000000000000000) + (248583871 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12522

/-! A coarse bound on the actual paper statistics constant at dimension 12523. -/
namespace BstLean.Part266.Row12523
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12521 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12521 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12521 128 ≤ (12775 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12775 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12523) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12523 : ℕ))
    (by norm_num : (12523 : ℕ) ≤ 16384)
  have ht : paperTail256 12523 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12523 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12523 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12523 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12523 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12523 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12521 128 * √(2 / (12523 : ℝ)) *
      (√(12523 : ℝ) + paperT0 12523 + paperTail256 12523) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12523 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12523 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12523 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12521 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12521 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12523 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12523

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12523
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12523 (61 / 100) 162 (17 / (100 * 12523)) (26 / (10 * 12523)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12523 (61 / 100) 162 (17 / (100 * 12523)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (497043091 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (15876167 / 10000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (179036273 / 31250000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12523 / 12523 * (61 / 100)) ^ 4 * inverseRadius8 (12523 - 1) /
            envelopeGap 12523 (61 / 100) 162 (17 / (100 * 12523)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12523

namespace BstLean.Part266.Row12523
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12523 162 ≤ (118659097 / 25000000000000000)
  f1 : (tableEnvelope C).f1 12523 162 ≤ (1583467317 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (190293463 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12523 162 ≤ (1912038873 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12523 162 ≤ (1360379097 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12523 162 ≤ (497048641 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (497043091 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (497043091 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (15876167 / 10000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (179036273 / 31250000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3684429 / 1000000000) : ℝ) ≤ √(17 / (100 * 12523) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12523) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (557361581 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19922454041 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12523) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12523) ≤ (7058081 / 62500000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12523) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12523 * (162 : ℝ) ^ 2 + 26 / (10 * 12523) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12523) : ℝ)) (tA 12523 * 162 ^ 2 + 26 / (10 * 12523)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3684429 / 1000000000))) * ((497043091 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3684429 / 1000000000)) ^ 3) * ((15876167 / 10000000000000000000000))) + ((179036273 / 31250000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3684429 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12523) : ℝ)) d.D d.V d.P (√(tA 12523) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3684429 / 1000000000)) ^ 2 * (((557361581 / 250000000000000)) * ((19922454041 / 500000000000000000)))) + ((179036273 / 31250000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12523) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3684429 / 1000000000)) * ((497043091 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12523) : ℝ)) (tA 12523 * 162 ^ 2 + 26 / (10 * 12523)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((497043091 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3684429 / 1000000000)) ^ 2) * ((15876167 / 10000000000000000000000)) + ((179036273 / 31250000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12523) : ℝ)) (√(26 / (10 * 12523) : ℝ)) d.D d.V d.P (√(tA 12523) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3684429 / 1000000000)) * (((557361581 / 250000000000000)) * ((19922454041 / 500000000000000000))) + ((179036273 / 31250000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12523) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((497043091 / 100000000000000000000) : ℝ) + ((179036273 / 31250000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12523

namespace BstLean.Part266.Row12523
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12523 162 ∧
    0 ≤ (tableEnvelope C).f1 12523 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12523 162 ∧
    0 ≤ (tableEnvelope C).w1 12523 162 ∧ 0 ≤ (tableEnvelope C).w2 12523 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12523 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12523 162 ∧ 0 ≤ d.f1 12523 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12523 162 ∧ 0 ≤ d.w1 12523 162 ∧ 0 ≤ d.w2 12523 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12523 ≤ 2 * (228 / 100 : ℝ) / 12523 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12523 ≤ 2 * (370 / 100 : ℝ) / 12523 := by
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
    (completeRAData (tableEnvelope C) 12523 162).locationBound 12523 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12523 162).energyBound 12523 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12523 162) (d.f1 12523 162) d.f2 ≤
      32 * (((118659097 / 25000000000000000) : ℝ) + (1583467317 / 1000000000000000000) + (190293463 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12523 162) (d.w1 12523 162)
      (d.w2 12523 162) ≤
      32 * (((1912038873 / 100000000000000000000) : ℝ) + (1360379097 / 100000000000000000000) + (497048641 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12523 162) (d.f1 12523 162) d.f2 ≤
      ((118659097 / 25000000000000000) : ℝ) ^ 2 + 2 * ((118659097 / 25000000000000000)) * ((1583467317 / 1000000000000000000)) * (126 / 100) +
      2 * (((1583467317 / 1000000000000000000)) ^ 2 + 2 * ((118659097 / 25000000000000000)) * ((190293463 / 500000000000000000))) +
      6 * ((1583467317 / 1000000000000000000)) * ((190293463 / 500000000000000000)) * (126 / 100) + 8 * ((190293463 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12523 162) (d.f1 12523 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12523 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12523 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12523 162) (d.f1 12523 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12523 162) (d.w1 12523 162) (d.w2 12523 162)
  have hwexpr0 : 0 ≤ d.w0 12523 162 + d.w1 12523 162 * √(π / 2) +
      2 * d.w2 12523 162 + energyR16 12523 *
      radiusPolynomialRoot16 (d.w0 12523 162) (d.w1 12523 162) (d.w2 12523 162) := by
    positivity
  constructor
  · change (12523 : ℝ) ^ 8 * (mA 12523 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12523 162) (d.f1 12523 162) d.f2 + locationR16 12523 *
        radiusPolynomialRoot16 (d.f0 12523 162) (d.f1 12523 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12523 : ℝ) ^ 8 * (mA 12523 : ℝ) ^ 8 *
        ((((118659097 / 25000000000000000) : ℝ) ^ 2 + 2 * ((118659097 / 25000000000000000)) * ((1583467317 / 1000000000000000000)) * (126 / 100) +
          2 * (((1583467317 / 1000000000000000000)) ^ 2 + 2 * ((118659097 / 25000000000000000)) * ((190293463 / 500000000000000000))) +
          6 * ((1583467317 / 1000000000000000000)) * ((190293463 / 500000000000000000)) * (126 / 100) + 8 * ((190293463 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12523) *
          (32 * (((118659097 / 25000000000000000) : ℝ) + (1583467317 / 1000000000000000000) + (190293463 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12523 : ℝ) ^ 16 *
      (d.w0 12523 162 + d.w1 12523 162 * √(π / 2) + 2 * d.w2 12523 162 +
        energyR16 12523 * radiusPolynomialRoot16 (d.w0 12523 162) (d.w1 12523 162)
          (d.w2 12523 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12523 : ℝ) ^ 16 *
        (((1912038873 / 100000000000000000000) : ℝ) + ((1360379097 / 100000000000000000000)) * (126 / 100) + 2 * ((497048641 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12523) *
          (32 * (((1912038873 / 100000000000000000000) : ℝ) + (1360379097 / 100000000000000000000) + (497048641 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12523

/-! A coarse bound on the actual paper statistics constant at dimension 12524. -/
namespace BstLean.Part266.Row12524
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12522 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12522 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12522 128 ≤ (12776 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12776 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12524) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12524 : ℕ))
    (by norm_num : (12524 : ℕ) ≤ 16384)
  have ht : paperTail256 12524 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12524 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12524 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12524 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12524 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12524 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12522 128 * √(2 / (12524 : ℝ)) *
      (√(12524 : ℝ) + paperT0 12524 + paperTail256 12524) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12524 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12524 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12524 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12522 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12522 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12524 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12524

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12524
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12524 (61 / 100) 162 (17 / (100 * 12524)) (26 / (10 * 12524)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12524 (61 / 100) 162 (17 / (100 * 12524)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (3882219 / 781250000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1587109677 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5725465931 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12524 / 12524 * (61 / 100)) ^ 4 * inverseRadius8 (12524 - 1) /
            envelopeGap 12524 (61 / 100) 162 (17 / (100 * 12524)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12524

namespace BstLean.Part266.Row12524
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12524 162 ≤ (237270803 / 50000000000000000)
  f1 : (tableEnvelope C).f1 12524 162 ≤ (316630229 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (11890967 / 31250000000000000)
  w0 : (tableEnvelope C).w0 12524 162 ≤ (597369 / 31250000000000000)
  w1 : (tableEnvelope C).w1 12524 162 ≤ (1360053203 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12524 162 ≤ (496929579 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (3882219 / 781250000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (3882219 / 781250000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1587109677 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5725465931 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1842141 / 500000000) : ℝ) ≤ √(17 / (100 * 12524) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12524) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2229179293 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39838545117 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12524) * 162 ≤ 186 / 10000 := by
    have hs : √(tA 12524) ≤ (112920279 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12524) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12524 * (162 : ℝ) ^ 2 + 26 / (10 * 12524) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12524) : ℝ)) (tA 12524 * 162 ^ 2 + 26 / (10 * 12524)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1842141 / 500000000))) * ((3882219 / 781250000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1842141 / 500000000)) ^ 3) * ((1587109677 / 1000000000000000000000000))) + ((5725465931 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1842141 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12524) : ℝ)) d.D d.V d.P (√(tA 12524) * 162) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1842141 / 500000000)) ^ 2 * (((2229179293 / 1000000000000000)) * ((39838545117 / 1000000000000000000)))) + ((5725465931 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12524) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1842141 / 500000000)) * ((3882219 / 781250000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12524) : ℝ)) (tA 12524 * 162 ^ 2 + 26 / (10 * 12524)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((3882219 / 781250000000000000) : ℝ) + (24198 / 100000) / (2 * ((1842141 / 500000000)) ^ 2) * ((1587109677 / 1000000000000000000000000)) + ((5725465931 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12524) : ℝ)) (√(26 / (10 * 12524) : ℝ)) d.D d.V d.P (√(tA 12524) * 162) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1842141 / 500000000)) * (((2229179293 / 1000000000000000)) * ((39838545117 / 1000000000000000000))) + ((5725465931 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12524) * 162) ≤ _
    unfold AW2
    calc
      _ ≤ ((3882219 / 781250000000000000) : ℝ) + ((5725465931 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12524

namespace BstLean.Part266.Row12524
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12524 162 ∧
    0 ≤ (tableEnvelope C).f1 12524 162 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12524 162 ∧
    0 ≤ (tableEnvelope C).w1 12524 162 ∧ 0 ≤ (tableEnvelope C).w2 12524 162 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12524 * (162 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12524 162 ∧ 0 ≤ d.f1 12524 162 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12524 162 ∧ 0 ≤ d.w1 12524 162 ∧ 0 ≤ d.w2 12524 162
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12524 ≤ 2 * (228 / 100 : ℝ) / 12524 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12524 ≤ 2 * (370 / 100 : ℝ) / 12524 := by
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
    (completeRAData (tableEnvelope C) 12524 162).locationBound 12524 162 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12524 162).energyBound 12524 162 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12524 162) (d.f1 12524 162) d.f2 ≤
      32 * (((237270803 / 50000000000000000) : ℝ) + (316630229 / 200000000000000000) + (11890967 / 31250000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12524 162) (d.w1 12524 162)
      (d.w2 12524 162) ≤
      32 * (((597369 / 31250000000000000) : ℝ) + (1360053203 / 100000000000000000000) + (496929579 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12524 162) (d.f1 12524 162) d.f2 ≤
      ((237270803 / 50000000000000000) : ℝ) ^ 2 + 2 * ((237270803 / 50000000000000000)) * ((316630229 / 200000000000000000)) * (126 / 100) +
      2 * (((316630229 / 200000000000000000)) ^ 2 + 2 * ((237270803 / 50000000000000000)) * ((11890967 / 31250000000000000))) +
      6 * ((316630229 / 200000000000000000)) * ((11890967 / 31250000000000000)) * (126 / 100) + 8 * ((11890967 / 31250000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12524 162) (d.f1 12524 162) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12524 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12524 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12524 162) (d.f1 12524 162) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12524 162) (d.w1 12524 162) (d.w2 12524 162)
  have hwexpr0 : 0 ≤ d.w0 12524 162 + d.w1 12524 162 * √(π / 2) +
      2 * d.w2 12524 162 + energyR16 12524 *
      radiusPolynomialRoot16 (d.w0 12524 162) (d.w1 12524 162) (d.w2 12524 162) := by
    positivity
  constructor
  · change (12524 : ℝ) ^ 8 * (mA 12524 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12524 162) (d.f1 12524 162) d.f2 + locationR16 12524 *
        radiusPolynomialRoot16 (d.f0 12524 162) (d.f1 12524 162) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12524 : ℝ) ^ 8 * (mA 12524 : ℝ) ^ 8 *
        ((((237270803 / 50000000000000000) : ℝ) ^ 2 + 2 * ((237270803 / 50000000000000000)) * ((316630229 / 200000000000000000)) * (126 / 100) +
          2 * (((316630229 / 200000000000000000)) ^ 2 + 2 * ((237270803 / 50000000000000000)) * ((11890967 / 31250000000000000))) +
          6 * ((316630229 / 200000000000000000)) * ((11890967 / 31250000000000000)) * (126 / 100) + 8 * ((11890967 / 31250000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12524) *
          (32 * (((237270803 / 50000000000000000) : ℝ) + (316630229 / 200000000000000000) + (11890967 / 31250000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12524 : ℝ) ^ 16 *
      (d.w0 12524 162 + d.w1 12524 162 * √(π / 2) + 2 * d.w2 12524 162 +
        energyR16 12524 * radiusPolynomialRoot16 (d.w0 12524 162) (d.w1 12524 162)
          (d.w2 12524 162)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12524 : ℝ) ^ 16 *
        (((597369 / 31250000000000000) : ℝ) + ((1360053203 / 100000000000000000000)) * (126 / 100) + 2 * ((496929579 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12524) *
          (32 * (((597369 / 31250000000000000) : ℝ) + (1360053203 / 100000000000000000000) + (496929579 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12524
