import BstLean.Part266Shard22Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12900. -/
namespace BstLean.Part266.Row12900
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12898 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12898 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12898 128 ≤ (13152 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13152 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12900) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12900 : ℕ))
    (by norm_num : (12900 : ℕ) ≤ 16384)
  have ht : paperTail256 12900 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12900 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12900 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12900 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12900 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12900 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12898 128 * √(2 / (12900 : ℝ)) *
      (√(12900 : ℝ) + paperT0 12900 + paperTail256 12900) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12900 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12900 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12900 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12898 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12898 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12900 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12900

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12900
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12900 (61 / 100) 164 (17 / (100 * 12900)) (26 / (10 * 12900)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12900 (61 / 100) 164 (17 / (100 * 12900)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (90944831 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1409997401 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2256382127 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12900 / 12900 * (61 / 100)) ^ 4 * inverseRadius8 (12900 - 1) /
            envelopeGap 12900 (61 / 100) 164 (17 / (100 * 12900)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12900

namespace BstLean.Part266.Row12900
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12900 164 ≤ (4407126077 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12900 164 ≤ (367572997 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (44173159 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12900 164 ≤ (174924467 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12900 164 ≤ (155569279 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 12900 164 ≤ (454728527 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (90944831 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (90944831 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1409997401 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2256382127 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((226887 / 62500000) : ℝ) ≤ √(17 / (100 * 12900) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12900) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2132426213 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4693741513 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12900) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12900) ≤ (109628959 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12900) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12900 * (164 : ℝ) ^ 2 + 26 / (10 * 12900) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12900) : ℝ)) (tA 12900 * 164 ^ 2 + 26 / (10 * 12900)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((226887 / 62500000))) * ((90944831 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((226887 / 62500000)) ^ 3) * ((1409997401 / 1000000000000000000000000))) + ((2256382127 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((226887 / 62500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12900) : ℝ)) d.D d.V d.P (√(tA 12900) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((226887 / 62500000)) ^ 2 * (((2132426213 / 1000000000000000)) * ((4693741513 / 125000000000000000)))) + ((2256382127 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12900) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((226887 / 62500000)) * ((90944831 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12900) : ℝ)) (tA 12900 * 164 ^ 2 + 26 / (10 * 12900)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((90944831 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((226887 / 62500000)) ^ 2) * ((1409997401 / 1000000000000000000000000)) + ((2256382127 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12900) : ℝ)) (√(26 / (10 * 12900) : ℝ)) d.D d.V d.P (√(tA 12900) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((226887 / 62500000)) * (((2132426213 / 1000000000000000)) * ((4693741513 / 125000000000000000))) + ((2256382127 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12900) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((90944831 / 20000000000000000000) : ℝ) + ((2256382127 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12900

namespace BstLean.Part266.Row12900
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12900 164 ∧
    0 ≤ (tableEnvelope C).f1 12900 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12900 164 ∧
    0 ≤ (tableEnvelope C).w1 12900 164 ∧ 0 ≤ (tableEnvelope C).w2 12900 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12900 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12900 164 ∧ 0 ≤ d.f1 12900 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12900 164 ∧ 0 ≤ d.w1 12900 164 ∧ 0 ≤ d.w2 12900 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12900 ≤ 2 * (228 / 100 : ℝ) / 12900 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12900 ≤ 2 * (370 / 100 : ℝ) / 12900 := by
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
    (completeRAData (tableEnvelope C) 12900 164).locationBound 12900 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12900 164).energyBound 12900 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12900 164) (d.f1 12900 164) d.f2 ≤
      32 * (((4407126077 / 1000000000000000000) : ℝ) + (367572997 / 250000000000000000) + (44173159 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12900 164) (d.w1 12900 164)
      (d.w2 12900 164) ≤
      32 * (((174924467 / 10000000000000000000) : ℝ) + (155569279 / 12500000000000000000) + (454728527 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12900 164) (d.f1 12900 164) d.f2 ≤
      ((4407126077 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4407126077 / 1000000000000000000)) * ((367572997 / 250000000000000000)) * (126 / 100) +
      2 * (((367572997 / 250000000000000000)) ^ 2 + 2 * ((4407126077 / 1000000000000000000)) * ((44173159 / 125000000000000000))) +
      6 * ((367572997 / 250000000000000000)) * ((44173159 / 125000000000000000)) * (126 / 100) + 8 * ((44173159 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12900 164) (d.f1 12900 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12900 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12900 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12900 164) (d.f1 12900 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12900 164) (d.w1 12900 164) (d.w2 12900 164)
  have hwexpr0 : 0 ≤ d.w0 12900 164 + d.w1 12900 164 * √(π / 2) +
      2 * d.w2 12900 164 + energyR16 12900 *
      radiusPolynomialRoot16 (d.w0 12900 164) (d.w1 12900 164) (d.w2 12900 164) := by
    positivity
  constructor
  · change (12900 : ℝ) ^ 8 * (mA 12900 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12900 164) (d.f1 12900 164) d.f2 + locationR16 12900 *
        radiusPolynomialRoot16 (d.f0 12900 164) (d.f1 12900 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12900 : ℝ) ^ 8 * (mA 12900 : ℝ) ^ 8 *
        ((((4407126077 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4407126077 / 1000000000000000000)) * ((367572997 / 250000000000000000)) * (126 / 100) +
          2 * (((367572997 / 250000000000000000)) ^ 2 + 2 * ((4407126077 / 1000000000000000000)) * ((44173159 / 125000000000000000))) +
          6 * ((367572997 / 250000000000000000)) * ((44173159 / 125000000000000000)) * (126 / 100) + 8 * ((44173159 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12900) *
          (32 * (((4407126077 / 1000000000000000000) : ℝ) + (367572997 / 250000000000000000) + (44173159 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12900 : ℝ) ^ 16 *
      (d.w0 12900 164 + d.w1 12900 164 * √(π / 2) + 2 * d.w2 12900 164 +
        energyR16 12900 * radiusPolynomialRoot16 (d.w0 12900 164) (d.w1 12900 164)
          (d.w2 12900 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12900 : ℝ) ^ 16 *
        (((174924467 / 10000000000000000000) : ℝ) + ((155569279 / 12500000000000000000)) * (126 / 100) + 2 * ((454728527 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12900) *
          (32 * (((174924467 / 10000000000000000000) : ℝ) + (155569279 / 12500000000000000000) + (454728527 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12900

/-! A coarse bound on the actual paper statistics constant at dimension 12901. -/
namespace BstLean.Part266.Row12901
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12899 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12899 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12899 128 ≤ (13153 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13153 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12901) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12901 : ℕ))
    (by norm_num : (12901 : ℕ) ≤ 16384)
  have ht : paperTail256 12901 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12901 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12901 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12901 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12901 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12901 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12899 128 * √(2 / (12901 : ℝ)) *
      (√(12901 : ℝ) + paperT0 12901 + paperTail256 12901) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12901 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12901 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12901 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12899 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12899 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12901 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12901

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12901
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12901 (61 / 100) 164 (17 / (100 * 12901)) (26 / (10 * 12901)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12901 (61 / 100) 164 (17 / (100 * 12901)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (28413651 / 6250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (70478013 / 50000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4509939889 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12901 / 12901 * (61 / 100)) ^ 4 * inverseRadius8 (12901 - 1) /
            envelopeGap 12901 (61 / 100) 164 (17 / (100 * 12901)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12901

namespace BstLean.Part266.Row12901
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12901 164 ≤ (4406273107 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12901 164 ≤ (1470007313 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (17665841 / 50000000000000000)
  w0 : (tableEnvelope C).w0 12901 164 ≤ (874419063 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12901 164 ≤ (622132467 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12901 164 ≤ (90924557 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (28413651 / 6250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (28413651 / 6250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (70478013 / 50000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4509939889 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3630051 / 1000000000) : ℝ) ≤ √(17 / (100 * 12901) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12901) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2132178267 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37544110857 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12901) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12901) ≤ (109620461 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12901) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12901 * (164 : ℝ) ^ 2 + 26 / (10 * 12901) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12901) : ℝ)) (tA 12901 * 164 ^ 2 + 26 / (10 * 12901)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3630051 / 1000000000))) * ((28413651 / 6250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3630051 / 1000000000)) ^ 3) * ((70478013 / 50000000000000000000000))) + ((4509939889 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3630051 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12901) : ℝ)) d.D d.V d.P (√(tA 12901) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3630051 / 1000000000)) ^ 2 * (((2132178267 / 1000000000000000)) * ((37544110857 / 1000000000000000000)))) + ((4509939889 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12901) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3630051 / 1000000000)) * ((28413651 / 6250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12901) : ℝ)) (tA 12901 * 164 ^ 2 + 26 / (10 * 12901)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((28413651 / 6250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3630051 / 1000000000)) ^ 2) * ((70478013 / 50000000000000000000000)) + ((4509939889 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12901) : ℝ)) (√(26 / (10 * 12901) : ℝ)) d.D d.V d.P (√(tA 12901) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3630051 / 1000000000)) * (((2132178267 / 1000000000000000)) * ((37544110857 / 1000000000000000000))) + ((4509939889 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12901) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((28413651 / 6250000000000000000) : ℝ) + ((4509939889 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12901

namespace BstLean.Part266.Row12901
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12901 164 ∧
    0 ≤ (tableEnvelope C).f1 12901 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12901 164 ∧
    0 ≤ (tableEnvelope C).w1 12901 164 ∧ 0 ≤ (tableEnvelope C).w2 12901 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12901 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12901 164 ∧ 0 ≤ d.f1 12901 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12901 164 ∧ 0 ≤ d.w1 12901 164 ∧ 0 ≤ d.w2 12901 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12901 ≤ 2 * (228 / 100 : ℝ) / 12901 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12901 ≤ 2 * (370 / 100 : ℝ) / 12901 := by
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
    (completeRAData (tableEnvelope C) 12901 164).locationBound 12901 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12901 164).energyBound 12901 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12901 164) (d.f1 12901 164) d.f2 ≤
      32 * (((4406273107 / 1000000000000000000) : ℝ) + (1470007313 / 1000000000000000000) + (17665841 / 50000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12901 164) (d.w1 12901 164)
      (d.w2 12901 164) ≤
      32 * (((874419063 / 50000000000000000000) : ℝ) + (622132467 / 50000000000000000000) + (90924557 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12901 164) (d.f1 12901 164) d.f2 ≤
      ((4406273107 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4406273107 / 1000000000000000000)) * ((1470007313 / 1000000000000000000)) * (126 / 100) +
      2 * (((1470007313 / 1000000000000000000)) ^ 2 + 2 * ((4406273107 / 1000000000000000000)) * ((17665841 / 50000000000000000))) +
      6 * ((1470007313 / 1000000000000000000)) * ((17665841 / 50000000000000000)) * (126 / 100) + 8 * ((17665841 / 50000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12901 164) (d.f1 12901 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12901 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12901 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12901 164) (d.f1 12901 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12901 164) (d.w1 12901 164) (d.w2 12901 164)
  have hwexpr0 : 0 ≤ d.w0 12901 164 + d.w1 12901 164 * √(π / 2) +
      2 * d.w2 12901 164 + energyR16 12901 *
      radiusPolynomialRoot16 (d.w0 12901 164) (d.w1 12901 164) (d.w2 12901 164) := by
    positivity
  constructor
  · change (12901 : ℝ) ^ 8 * (mA 12901 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12901 164) (d.f1 12901 164) d.f2 + locationR16 12901 *
        radiusPolynomialRoot16 (d.f0 12901 164) (d.f1 12901 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12901 : ℝ) ^ 8 * (mA 12901 : ℝ) ^ 8 *
        ((((4406273107 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4406273107 / 1000000000000000000)) * ((1470007313 / 1000000000000000000)) * (126 / 100) +
          2 * (((1470007313 / 1000000000000000000)) ^ 2 + 2 * ((4406273107 / 1000000000000000000)) * ((17665841 / 50000000000000000))) +
          6 * ((1470007313 / 1000000000000000000)) * ((17665841 / 50000000000000000)) * (126 / 100) + 8 * ((17665841 / 50000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12901) *
          (32 * (((4406273107 / 1000000000000000000) : ℝ) + (1470007313 / 1000000000000000000) + (17665841 / 50000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12901 : ℝ) ^ 16 *
      (d.w0 12901 164 + d.w1 12901 164 * √(π / 2) + 2 * d.w2 12901 164 +
        energyR16 12901 * radiusPolynomialRoot16 (d.w0 12901 164) (d.w1 12901 164)
          (d.w2 12901 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12901 : ℝ) ^ 16 *
        (((874419063 / 50000000000000000000) : ℝ) + ((622132467 / 50000000000000000000)) * (126 / 100) + 2 * ((90924557 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12901) *
          (32 * (((874419063 / 50000000000000000000) : ℝ) + (622132467 / 50000000000000000000) + (90924557 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12901

/-! A coarse bound on the actual paper statistics constant at dimension 12902. -/
namespace BstLean.Part266.Row12902
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12900 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12900 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12900 128 ≤ (13154 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13154 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12902) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12902 : ℕ))
    (by norm_num : (12902 : ℕ) ≤ 16384)
  have ht : paperTail256 12902 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12902 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12902 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12902 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12902 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12902 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12900 128 * √(2 / (12902 : ℝ)) *
      (√(12902 : ℝ) + paperT0 12902 + paperTail256 12902) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12902 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12902 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12902 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12900 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12900 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12902 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12902

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12902
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12902 (61 / 100) 164 (17 / (100 * 12902)) (26 / (10 * 12902)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12902 (61 / 100) 164 (17 / (100 * 12902)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (45451271 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1409123289 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (901423503 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12902 / 12902 * (61 / 100)) ^ 4 * inverseRadius8 (12902 - 1) /
            envelopeGap 12902 (61 / 100) 164 (17 / (100 * 12902)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12902

namespace BstLean.Part266.Row12902
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12902 164 ≤ (4405420427 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12902 164 ≤ (146972273 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (35324839 / 100000000000000000)
  w0 : (tableEnvelope C).w0 12902 164 ≤ (1748431721 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12902 164 ≤ (310993933 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12902 164 ≤ (113629269 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (45451271 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (45451271 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1409123289 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (901423503 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((362991 / 100000000) : ℝ) ≤ √(17 / (100 * 12902) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12902) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (213193037 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37538290971 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12902) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12902) ≤ (21922393 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12902) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12902 * (164 : ℝ) ^ 2 + 26 / (10 * 12902) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12902) : ℝ)) (tA 12902 * 164 ^ 2 + 26 / (10 * 12902)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((362991 / 100000000))) * ((45451271 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((362991 / 100000000)) ^ 3) * ((1409123289 / 1000000000000000000000000))) + ((901423503 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((362991 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12902) : ℝ)) d.D d.V d.P (√(tA 12902) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((362991 / 100000000)) ^ 2 * (((213193037 / 100000000000000)) * ((37538290971 / 1000000000000000000)))) + ((901423503 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12902) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((362991 / 100000000)) * ((45451271 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12902) : ℝ)) (tA 12902 * 164 ^ 2 + 26 / (10 * 12902)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((45451271 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((362991 / 100000000)) ^ 2) * ((1409123289 / 1000000000000000000000000)) + ((901423503 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12902) : ℝ)) (√(26 / (10 * 12902) : ℝ)) d.D d.V d.P (√(tA 12902) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((362991 / 100000000)) * (((213193037 / 100000000000000)) * ((37538290971 / 1000000000000000000))) + ((901423503 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12902) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((45451271 / 10000000000000000000) : ℝ) + ((901423503 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12902

namespace BstLean.Part266.Row12902
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12902 164 ∧
    0 ≤ (tableEnvelope C).f1 12902 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12902 164 ∧
    0 ≤ (tableEnvelope C).w1 12902 164 ∧ 0 ≤ (tableEnvelope C).w2 12902 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12902 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12902 164 ∧ 0 ≤ d.f1 12902 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12902 164 ∧ 0 ≤ d.w1 12902 164 ∧ 0 ≤ d.w2 12902 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12902 ≤ 2 * (228 / 100 : ℝ) / 12902 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12902 ≤ 2 * (370 / 100 : ℝ) / 12902 := by
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
    (completeRAData (tableEnvelope C) 12902 164).locationBound 12902 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12902 164).energyBound 12902 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12902 164) (d.f1 12902 164) d.f2 ≤
      32 * (((4405420427 / 1000000000000000000) : ℝ) + (146972273 / 100000000000000000) + (35324839 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12902 164) (d.w1 12902 164)
      (d.w2 12902 164) ≤
      32 * (((1748431721 / 100000000000000000000) : ℝ) + (310993933 / 25000000000000000000) + (113629269 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12902 164) (d.f1 12902 164) d.f2 ≤
      ((4405420427 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4405420427 / 1000000000000000000)) * ((146972273 / 100000000000000000)) * (126 / 100) +
      2 * (((146972273 / 100000000000000000)) ^ 2 + 2 * ((4405420427 / 1000000000000000000)) * ((35324839 / 100000000000000000))) +
      6 * ((146972273 / 100000000000000000)) * ((35324839 / 100000000000000000)) * (126 / 100) + 8 * ((35324839 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12902 164) (d.f1 12902 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12902 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12902 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12902 164) (d.f1 12902 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12902 164) (d.w1 12902 164) (d.w2 12902 164)
  have hwexpr0 : 0 ≤ d.w0 12902 164 + d.w1 12902 164 * √(π / 2) +
      2 * d.w2 12902 164 + energyR16 12902 *
      radiusPolynomialRoot16 (d.w0 12902 164) (d.w1 12902 164) (d.w2 12902 164) := by
    positivity
  constructor
  · change (12902 : ℝ) ^ 8 * (mA 12902 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12902 164) (d.f1 12902 164) d.f2 + locationR16 12902 *
        radiusPolynomialRoot16 (d.f0 12902 164) (d.f1 12902 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12902 : ℝ) ^ 8 * (mA 12902 : ℝ) ^ 8 *
        ((((4405420427 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4405420427 / 1000000000000000000)) * ((146972273 / 100000000000000000)) * (126 / 100) +
          2 * (((146972273 / 100000000000000000)) ^ 2 + 2 * ((4405420427 / 1000000000000000000)) * ((35324839 / 100000000000000000))) +
          6 * ((146972273 / 100000000000000000)) * ((35324839 / 100000000000000000)) * (126 / 100) + 8 * ((35324839 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12902) *
          (32 * (((4405420427 / 1000000000000000000) : ℝ) + (146972273 / 100000000000000000) + (35324839 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12902 : ℝ) ^ 16 *
      (d.w0 12902 164 + d.w1 12902 164 * √(π / 2) + 2 * d.w2 12902 164 +
        energyR16 12902 * radiusPolynomialRoot16 (d.w0 12902 164) (d.w1 12902 164)
          (d.w2 12902 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12902 : ℝ) ^ 16 *
        (((1748431721 / 100000000000000000000) : ℝ) + ((310993933 / 25000000000000000000)) * (126 / 100) + 2 * ((113629269 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12902) *
          (32 * (((1748431721 / 100000000000000000000) : ℝ) + (310993933 / 25000000000000000000) + (113629269 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12902

/-! A coarse bound on the actual paper statistics constant at dimension 12903. -/
namespace BstLean.Part266.Row12903
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12901 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12901 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12901 128 ≤ (13155 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13155 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12903) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12903 : ℕ))
    (by norm_num : (12903 : ℕ) ≤ 16384)
  have ht : paperTail256 12903 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12903 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12903 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12903 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12903 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12903 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12901 128 * √(2 / (12903 : ℝ)) *
      (√(12903 : ℝ) + paperT0 12903 + paperTail256 12903) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12903 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12903 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12903 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12901 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12901 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12903 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12903

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12903
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12903 (61 / 100) 164 (17 / (100 * 12903)) (26 / (10 * 12903)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12903 (61 / 100) 164 (17 / (100 * 12903)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (454407037 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1408686487 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4504297129 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12903 / 12903 * (61 / 100)) ^ 4 * inverseRadius8 (12903 - 1) /
            envelopeGap 12903 (61 / 100) 164 (17 / (100 * 12903)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12903

namespace BstLean.Part266.Row12903
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12903 164 ≤ (1101141133 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12903 164 ≤ (1469437427 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (176589941 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12903 164 ≤ (1748024741 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12903 164 ≤ (621843141 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12903 164 ≤ (454411401 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (454407037 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (454407037 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1408686487 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4504297129 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((362977 / 100000000) : ℝ) ≤ √(17 / (100 * 12903) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12903) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2131682521 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18766236217 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12903) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12903) ≤ (10960347 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12903) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12903 * (164 : ℝ) ^ 2 + 26 / (10 * 12903) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12903) : ℝ)) (tA 12903 * 164 ^ 2 + 26 / (10 * 12903)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((362977 / 100000000))) * ((454407037 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((362977 / 100000000)) ^ 3) * ((1408686487 / 1000000000000000000000000))) + ((4504297129 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((362977 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12903) : ℝ)) d.D d.V d.P (√(tA 12903) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((362977 / 100000000)) ^ 2 * (((2131682521 / 1000000000000000)) * ((18766236217 / 500000000000000000)))) + ((4504297129 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12903) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((362977 / 100000000)) * ((454407037 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12903) : ℝ)) (tA 12903 * 164 ^ 2 + 26 / (10 * 12903)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((454407037 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((362977 / 100000000)) ^ 2) * ((1408686487 / 1000000000000000000000000)) + ((4504297129 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12903) : ℝ)) (√(26 / (10 * 12903) : ℝ)) d.D d.V d.P (√(tA 12903) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((362977 / 100000000)) * (((2131682521 / 1000000000000000)) * ((18766236217 / 500000000000000000))) + ((4504297129 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12903) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((454407037 / 100000000000000000000) : ℝ) + ((4504297129 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12903

namespace BstLean.Part266.Row12903
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12903 164 ∧
    0 ≤ (tableEnvelope C).f1 12903 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12903 164 ∧
    0 ≤ (tableEnvelope C).w1 12903 164 ∧ 0 ≤ (tableEnvelope C).w2 12903 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12903 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12903 164 ∧ 0 ≤ d.f1 12903 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12903 164 ∧ 0 ≤ d.w1 12903 164 ∧ 0 ≤ d.w2 12903 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12903 ≤ 2 * (228 / 100 : ℝ) / 12903 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12903 ≤ 2 * (370 / 100 : ℝ) / 12903 := by
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
    (completeRAData (tableEnvelope C) 12903 164).locationBound 12903 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12903 164).energyBound 12903 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12903 164) (d.f1 12903 164) d.f2 ≤
      32 * (((1101141133 / 250000000000000000) : ℝ) + (1469437427 / 1000000000000000000) + (176589941 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12903 164) (d.w1 12903 164)
      (d.w2 12903 164) ≤
      32 * (((1748024741 / 100000000000000000000) : ℝ) + (621843141 / 50000000000000000000) + (454411401 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12903 164) (d.f1 12903 164) d.f2 ≤
      ((1101141133 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1101141133 / 250000000000000000)) * ((1469437427 / 1000000000000000000)) * (126 / 100) +
      2 * (((1469437427 / 1000000000000000000)) ^ 2 + 2 * ((1101141133 / 250000000000000000)) * ((176589941 / 500000000000000000))) +
      6 * ((1469437427 / 1000000000000000000)) * ((176589941 / 500000000000000000)) * (126 / 100) + 8 * ((176589941 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12903 164) (d.f1 12903 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12903 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12903 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12903 164) (d.f1 12903 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12903 164) (d.w1 12903 164) (d.w2 12903 164)
  have hwexpr0 : 0 ≤ d.w0 12903 164 + d.w1 12903 164 * √(π / 2) +
      2 * d.w2 12903 164 + energyR16 12903 *
      radiusPolynomialRoot16 (d.w0 12903 164) (d.w1 12903 164) (d.w2 12903 164) := by
    positivity
  constructor
  · change (12903 : ℝ) ^ 8 * (mA 12903 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12903 164) (d.f1 12903 164) d.f2 + locationR16 12903 *
        radiusPolynomialRoot16 (d.f0 12903 164) (d.f1 12903 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12903 : ℝ) ^ 8 * (mA 12903 : ℝ) ^ 8 *
        ((((1101141133 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1101141133 / 250000000000000000)) * ((1469437427 / 1000000000000000000)) * (126 / 100) +
          2 * (((1469437427 / 1000000000000000000)) ^ 2 + 2 * ((1101141133 / 250000000000000000)) * ((176589941 / 500000000000000000))) +
          6 * ((1469437427 / 1000000000000000000)) * ((176589941 / 500000000000000000)) * (126 / 100) + 8 * ((176589941 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12903) *
          (32 * (((1101141133 / 250000000000000000) : ℝ) + (1469437427 / 1000000000000000000) + (176589941 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12903 : ℝ) ^ 16 *
      (d.w0 12903 164 + d.w1 12903 164 * √(π / 2) + 2 * d.w2 12903 164 +
        energyR16 12903 * radiusPolynomialRoot16 (d.w0 12903 164) (d.w1 12903 164)
          (d.w2 12903 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12903 : ℝ) ^ 16 *
        (((1748024741 / 100000000000000000000) : ℝ) + ((621843141 / 50000000000000000000)) * (126 / 100) + 2 * ((454411401 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12903) *
          (32 * (((1748024741 / 100000000000000000000) : ℝ) + (621843141 / 50000000000000000000) + (454411401 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12903

/-! A coarse bound on the actual paper statistics constant at dimension 12904. -/
namespace BstLean.Part266.Row12904
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12902 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12902 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12902 128 ≤ (13156 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13156 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12904) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12904 : ℕ))
    (by norm_num : (12904 : ℕ) ≤ 16384)
  have ht : paperTail256 12904 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12904 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12904 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12904 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12904 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12904 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12902 128 * √(2 / (12904 : ℝ)) *
      (√(12904 : ℝ) + paperT0 12904 + paperTail256 12904) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12904 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12904 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12904 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12902 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12902 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12904 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12904

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12904
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12904 (61 / 100) 164 (17 / (100 * 12904)) (26 / (10 * 12904)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12904 (61 / 100) 164 (17 / (100 * 12904)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (454301397 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (704124927 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4501478731 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12904 / 12904 * (61 / 100)) ^ 4 * inverseRadius8 (12904 - 1) /
            envelopeGap 12904 (61 / 100) 164 (17 / (100 * 12904)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12904

namespace BstLean.Part266.Row12904
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12904 164 ≤ (1100928107 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12904 164 ≤ (734576513 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (88277873 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12904 164 ≤ (1747618611 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12904 164 ≤ (155424659 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 12904 164 ≤ (227152879 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (454301397 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (454301397 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (704124927 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4501478731 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3629629 / 1000000000) : ℝ) ≤ √(17 / (100 * 12904) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12904) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1065717361 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37526655247 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12904) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12904) ≤ (3424843 / 31250000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12904) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12904 * (164 : ℝ) ^ 2 + 26 / (10 * 12904) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12904) : ℝ)) (tA 12904 * 164 ^ 2 + 26 / (10 * 12904)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3629629 / 1000000000))) * ((454301397 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3629629 / 1000000000)) ^ 3) * ((704124927 / 500000000000000000000000))) + ((4501478731 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3629629 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12904) : ℝ)) d.D d.V d.P (√(tA 12904) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3629629 / 1000000000)) ^ 2 * (((1065717361 / 500000000000000)) * ((37526655247 / 1000000000000000000)))) + ((4501478731 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12904) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3629629 / 1000000000)) * ((454301397 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12904) : ℝ)) (tA 12904 * 164 ^ 2 + 26 / (10 * 12904)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((454301397 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3629629 / 1000000000)) ^ 2) * ((704124927 / 500000000000000000000000)) + ((4501478731 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12904) : ℝ)) (√(26 / (10 * 12904) : ℝ)) d.D d.V d.P (√(tA 12904) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3629629 / 1000000000)) * (((1065717361 / 500000000000000)) * ((37526655247 / 1000000000000000000))) + ((4501478731 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12904) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((454301397 / 100000000000000000000) : ℝ) + ((4501478731 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12904

namespace BstLean.Part266.Row12904
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12904 164 ∧
    0 ≤ (tableEnvelope C).f1 12904 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12904 164 ∧
    0 ≤ (tableEnvelope C).w1 12904 164 ∧ 0 ≤ (tableEnvelope C).w2 12904 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12904 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12904 164 ∧ 0 ≤ d.f1 12904 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12904 164 ∧ 0 ≤ d.w1 12904 164 ∧ 0 ≤ d.w2 12904 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12904 ≤ 2 * (228 / 100 : ℝ) / 12904 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12904 ≤ 2 * (370 / 100 : ℝ) / 12904 := by
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
    (completeRAData (tableEnvelope C) 12904 164).locationBound 12904 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12904 164).energyBound 12904 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12904 164) (d.f1 12904 164) d.f2 ≤
      32 * (((1100928107 / 250000000000000000) : ℝ) + (734576513 / 500000000000000000) + (88277873 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12904 164) (d.w1 12904 164)
      (d.w2 12904 164) ≤
      32 * (((1747618611 / 100000000000000000000) : ℝ) + (155424659 / 12500000000000000000) + (227152879 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12904 164) (d.f1 12904 164) d.f2 ≤
      ((1100928107 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1100928107 / 250000000000000000)) * ((734576513 / 500000000000000000)) * (126 / 100) +
      2 * (((734576513 / 500000000000000000)) ^ 2 + 2 * ((1100928107 / 250000000000000000)) * ((88277873 / 250000000000000000))) +
      6 * ((734576513 / 500000000000000000)) * ((88277873 / 250000000000000000)) * (126 / 100) + 8 * ((88277873 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12904 164) (d.f1 12904 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12904 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12904 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12904 164) (d.f1 12904 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12904 164) (d.w1 12904 164) (d.w2 12904 164)
  have hwexpr0 : 0 ≤ d.w0 12904 164 + d.w1 12904 164 * √(π / 2) +
      2 * d.w2 12904 164 + energyR16 12904 *
      radiusPolynomialRoot16 (d.w0 12904 164) (d.w1 12904 164) (d.w2 12904 164) := by
    positivity
  constructor
  · change (12904 : ℝ) ^ 8 * (mA 12904 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12904 164) (d.f1 12904 164) d.f2 + locationR16 12904 *
        radiusPolynomialRoot16 (d.f0 12904 164) (d.f1 12904 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12904 : ℝ) ^ 8 * (mA 12904 : ℝ) ^ 8 *
        ((((1100928107 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1100928107 / 250000000000000000)) * ((734576513 / 500000000000000000)) * (126 / 100) +
          2 * (((734576513 / 500000000000000000)) ^ 2 + 2 * ((1100928107 / 250000000000000000)) * ((88277873 / 250000000000000000))) +
          6 * ((734576513 / 500000000000000000)) * ((88277873 / 250000000000000000)) * (126 / 100) + 8 * ((88277873 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12904) *
          (32 * (((1100928107 / 250000000000000000) : ℝ) + (734576513 / 500000000000000000) + (88277873 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12904 : ℝ) ^ 16 *
      (d.w0 12904 164 + d.w1 12904 164 * √(π / 2) + 2 * d.w2 12904 164 +
        energyR16 12904 * radiusPolynomialRoot16 (d.w0 12904 164) (d.w1 12904 164)
          (d.w2 12904 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12904 : ℝ) ^ 16 *
        (((1747618611 / 100000000000000000000) : ℝ) + ((155424659 / 12500000000000000000)) * (126 / 100) + 2 * ((227152879 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12904) *
          (32 * (((1747618611 / 100000000000000000000) : ℝ) + (155424659 / 12500000000000000000) + (227152879 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12904

/-! A coarse bound on the actual paper statistics constant at dimension 12905. -/
namespace BstLean.Part266.Row12905
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12903 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12903 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12903 128 ≤ (13157 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13157 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12905) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12905 : ℕ))
    (by norm_num : (12905 : ℕ) ≤ 16384)
  have ht : paperTail256 12905 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12905 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12905 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12905 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12905 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12905 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12903 128 * √(2 / (12905 : ℝ)) *
      (√(12905 : ℝ) + paperT0 12905 + paperTail256 12905) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12905 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12905 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12905 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12903 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12903 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12905 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12905

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12905
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12905 (61 / 100) 164 (17 / (100 * 12905)) (26 / (10 * 12905)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12905 (61 / 100) 164 (17 / (100 * 12905)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (454195789 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (140781339 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4498662319 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12905 / 12905 * (61 / 100)) ^ 4 * inverseRadius8 (12905 - 1) /
            envelopeGap 12905 (61 / 100) 164 (17 / (100 * 12905)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12905

namespace BstLean.Part266.Row12905
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12905 164 ≤ (1100715153 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12905 164 ≤ (1468868713 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (353043121 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12905 164 ≤ (1747212617 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12905 164 ≤ (621554177 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12905 164 ≤ (454200147 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (454195789 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (454195789 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (140781339 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4498662319 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((226843 / 62500000) : ℝ) ≤ √(17 / (100 * 12905) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12905) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (266398371 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3752083941 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12905) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12905) ≤ (109586483 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12905) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12905 * (164 : ℝ) ^ 2 + 26 / (10 * 12905) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12905) : ℝ)) (tA 12905 * 164 ^ 2 + 26 / (10 * 12905)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((226843 / 62500000))) * ((454195789 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((226843 / 62500000)) ^ 3) * ((140781339 / 100000000000000000000000))) + ((4498662319 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((226843 / 62500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12905) : ℝ)) d.D d.V d.P (√(tA 12905) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((226843 / 62500000)) ^ 2 * (((266398371 / 125000000000000)) * ((3752083941 / 100000000000000000)))) + ((4498662319 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12905) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((226843 / 62500000)) * ((454195789 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12905) : ℝ)) (tA 12905 * 164 ^ 2 + 26 / (10 * 12905)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((454195789 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((226843 / 62500000)) ^ 2) * ((140781339 / 100000000000000000000000)) + ((4498662319 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12905) : ℝ)) (√(26 / (10 * 12905) : ℝ)) d.D d.V d.P (√(tA 12905) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((226843 / 62500000)) * (((266398371 / 125000000000000)) * ((3752083941 / 100000000000000000))) + ((4498662319 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12905) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((454195789 / 100000000000000000000) : ℝ) + ((4498662319 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12905

namespace BstLean.Part266.Row12905
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12905 164 ∧
    0 ≤ (tableEnvelope C).f1 12905 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12905 164 ∧
    0 ≤ (tableEnvelope C).w1 12905 164 ∧ 0 ≤ (tableEnvelope C).w2 12905 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12905 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12905 164 ∧ 0 ≤ d.f1 12905 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12905 164 ∧ 0 ≤ d.w1 12905 164 ∧ 0 ≤ d.w2 12905 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12905 ≤ 2 * (228 / 100 : ℝ) / 12905 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12905 ≤ 2 * (370 / 100 : ℝ) / 12905 := by
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
    (completeRAData (tableEnvelope C) 12905 164).locationBound 12905 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12905 164).energyBound 12905 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12905 164) (d.f1 12905 164) d.f2 ≤
      32 * (((1100715153 / 250000000000000000) : ℝ) + (1468868713 / 1000000000000000000) + (353043121 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12905 164) (d.w1 12905 164)
      (d.w2 12905 164) ≤
      32 * (((1747212617 / 100000000000000000000) : ℝ) + (621554177 / 50000000000000000000) + (454200147 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12905 164) (d.f1 12905 164) d.f2 ≤
      ((1100715153 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1100715153 / 250000000000000000)) * ((1468868713 / 1000000000000000000)) * (126 / 100) +
      2 * (((1468868713 / 1000000000000000000)) ^ 2 + 2 * ((1100715153 / 250000000000000000)) * ((353043121 / 1000000000000000000))) +
      6 * ((1468868713 / 1000000000000000000)) * ((353043121 / 1000000000000000000)) * (126 / 100) + 8 * ((353043121 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12905 164) (d.f1 12905 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12905 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12905 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12905 164) (d.f1 12905 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12905 164) (d.w1 12905 164) (d.w2 12905 164)
  have hwexpr0 : 0 ≤ d.w0 12905 164 + d.w1 12905 164 * √(π / 2) +
      2 * d.w2 12905 164 + energyR16 12905 *
      radiusPolynomialRoot16 (d.w0 12905 164) (d.w1 12905 164) (d.w2 12905 164) := by
    positivity
  constructor
  · change (12905 : ℝ) ^ 8 * (mA 12905 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12905 164) (d.f1 12905 164) d.f2 + locationR16 12905 *
        radiusPolynomialRoot16 (d.f0 12905 164) (d.f1 12905 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12905 : ℝ) ^ 8 * (mA 12905 : ℝ) ^ 8 *
        ((((1100715153 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1100715153 / 250000000000000000)) * ((1468868713 / 1000000000000000000)) * (126 / 100) +
          2 * (((1468868713 / 1000000000000000000)) ^ 2 + 2 * ((1100715153 / 250000000000000000)) * ((353043121 / 1000000000000000000))) +
          6 * ((1468868713 / 1000000000000000000)) * ((353043121 / 1000000000000000000)) * (126 / 100) + 8 * ((353043121 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12905) *
          (32 * (((1100715153 / 250000000000000000) : ℝ) + (1468868713 / 1000000000000000000) + (353043121 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12905 : ℝ) ^ 16 *
      (d.w0 12905 164 + d.w1 12905 164 * √(π / 2) + 2 * d.w2 12905 164 +
        energyR16 12905 * radiusPolynomialRoot16 (d.w0 12905 164) (d.w1 12905 164)
          (d.w2 12905 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12905 : ℝ) ^ 16 *
        (((1747212617 / 100000000000000000000) : ℝ) + ((621554177 / 50000000000000000000)) * (126 / 100) + 2 * ((454200147 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12905) *
          (32 * (((1747212617 / 100000000000000000000) : ℝ) + (621554177 / 50000000000000000000) + (454200147 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12905

/-! A coarse bound on the actual paper statistics constant at dimension 12906. -/
namespace BstLean.Part266.Row12906
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12904 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12904 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12904 128 ≤ (13158 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13158 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12906) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12906 : ℕ))
    (by norm_num : (12906 : ℕ) ≤ 16384)
  have ht : paperTail256 12906 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12906 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12906 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12906 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12906 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12906 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12904 128 * √(2 / (12906 : ℝ)) *
      (√(12906 : ℝ) + paperT0 12906 + paperTail256 12906) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12906 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12906 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12906 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12904 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12904 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12906 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12906

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12906
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12906 (61 / 100) 164 (17 / (100 * 12906)) (26 / (10 * 12906)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12906 (61 / 100) 164 (17 / (100 * 12906)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (227045107 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (175922137 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4495847891 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12906 / 12906 * (61 / 100)) ^ 4 * inverseRadius8 (12906 - 1) /
            envelopeGap 12906 (61 / 100) 164 (17 / (100 * 12906)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12906

namespace BstLean.Part266.Row12906
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12906 164 ≤ (880401117 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12906 164 ≤ (734291841 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (176487337 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12906 164 ≤ (34936121 / 2000000000000000000)
  w1 : (tableEnvelope C).w1 12906 164 ≤ (1242819191 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12906 164 ≤ (45409457 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (227045107 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (227045107 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (175922137 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4495847891 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((907337 / 250000000) : ℝ) ≤ √(17 / (100 * 12906) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12906) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2130939263 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37515024937 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12906) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12906) ≤ (13697249 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12906) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12906 * (164 : ℝ) ^ 2 + 26 / (10 * 12906) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12906) : ℝ)) (tA 12906 * 164 ^ 2 + 26 / (10 * 12906)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((907337 / 250000000))) * ((227045107 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((907337 / 250000000)) ^ 3) * ((175922137 / 125000000000000000000000))) + ((4495847891 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((907337 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12906) : ℝ)) d.D d.V d.P (√(tA 12906) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((907337 / 250000000)) ^ 2 * (((2130939263 / 1000000000000000)) * ((37515024937 / 1000000000000000000)))) + ((4495847891 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12906) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((907337 / 250000000)) * ((227045107 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12906) : ℝ)) (tA 12906 * 164 ^ 2 + 26 / (10 * 12906)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((227045107 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((907337 / 250000000)) ^ 2) * ((175922137 / 125000000000000000000000)) + ((4495847891 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12906) : ℝ)) (√(26 / (10 * 12906) : ℝ)) d.D d.V d.P (√(tA 12906) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((907337 / 250000000)) * (((2130939263 / 1000000000000000)) * ((37515024937 / 1000000000000000000))) + ((4495847891 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12906) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((227045107 / 50000000000000000000) : ℝ) + ((4495847891 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12906

namespace BstLean.Part266.Row12906
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12906 164 ∧
    0 ≤ (tableEnvelope C).f1 12906 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12906 164 ∧
    0 ≤ (tableEnvelope C).w1 12906 164 ∧ 0 ≤ (tableEnvelope C).w2 12906 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12906 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12906 164 ∧ 0 ≤ d.f1 12906 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12906 164 ∧ 0 ≤ d.w1 12906 164 ∧ 0 ≤ d.w2 12906 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12906 ≤ 2 * (228 / 100 : ℝ) / 12906 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12906 ≤ 2 * (370 / 100 : ℝ) / 12906 := by
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
    (completeRAData (tableEnvelope C) 12906 164).locationBound 12906 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12906 164).energyBound 12906 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12906 164) (d.f1 12906 164) d.f2 ≤
      32 * (((880401117 / 200000000000000000) : ℝ) + (734291841 / 500000000000000000) + (176487337 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12906 164) (d.w1 12906 164)
      (d.w2 12906 164) ≤
      32 * (((34936121 / 2000000000000000000) : ℝ) + (1242819191 / 100000000000000000000) + (45409457 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12906 164) (d.f1 12906 164) d.f2 ≤
      ((880401117 / 200000000000000000) : ℝ) ^ 2 + 2 * ((880401117 / 200000000000000000)) * ((734291841 / 500000000000000000)) * (126 / 100) +
      2 * (((734291841 / 500000000000000000)) ^ 2 + 2 * ((880401117 / 200000000000000000)) * ((176487337 / 500000000000000000))) +
      6 * ((734291841 / 500000000000000000)) * ((176487337 / 500000000000000000)) * (126 / 100) + 8 * ((176487337 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12906 164) (d.f1 12906 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12906 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12906 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12906 164) (d.f1 12906 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12906 164) (d.w1 12906 164) (d.w2 12906 164)
  have hwexpr0 : 0 ≤ d.w0 12906 164 + d.w1 12906 164 * √(π / 2) +
      2 * d.w2 12906 164 + energyR16 12906 *
      radiusPolynomialRoot16 (d.w0 12906 164) (d.w1 12906 164) (d.w2 12906 164) := by
    positivity
  constructor
  · change (12906 : ℝ) ^ 8 * (mA 12906 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12906 164) (d.f1 12906 164) d.f2 + locationR16 12906 *
        radiusPolynomialRoot16 (d.f0 12906 164) (d.f1 12906 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12906 : ℝ) ^ 8 * (mA 12906 : ℝ) ^ 8 *
        ((((880401117 / 200000000000000000) : ℝ) ^ 2 + 2 * ((880401117 / 200000000000000000)) * ((734291841 / 500000000000000000)) * (126 / 100) +
          2 * (((734291841 / 500000000000000000)) ^ 2 + 2 * ((880401117 / 200000000000000000)) * ((176487337 / 500000000000000000))) +
          6 * ((734291841 / 500000000000000000)) * ((176487337 / 500000000000000000)) * (126 / 100) + 8 * ((176487337 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12906) *
          (32 * (((880401117 / 200000000000000000) : ℝ) + (734291841 / 500000000000000000) + (176487337 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12906 : ℝ) ^ 16 *
      (d.w0 12906 164 + d.w1 12906 164 * √(π / 2) + 2 * d.w2 12906 164 +
        energyR16 12906 * radiusPolynomialRoot16 (d.w0 12906 164) (d.w1 12906 164)
          (d.w2 12906 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12906 : ℝ) ^ 16 *
        (((34936121 / 2000000000000000000) : ℝ) + ((1242819191 / 100000000000000000000)) * (126 / 100) + 2 * ((45409457 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12906) *
          (32 * (((34936121 / 2000000000000000000) : ℝ) + (1242819191 / 100000000000000000000) + (45409457 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12906

/-! A coarse bound on the actual paper statistics constant at dimension 12907. -/
namespace BstLean.Part266.Row12907
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12905 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12905 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12905 128 ≤ (13159 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13159 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12907) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12907 : ℕ))
    (by norm_num : (12907 : ℕ) ≤ 16384)
  have ht : paperTail256 12907 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12907 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12907 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12907 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12907 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12907 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12905 128 * √(2 / (12907 : ℝ)) *
      (√(12907 : ℝ) + paperT0 12907 + paperTail256 12907) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12907 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12907 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12907 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12905 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12905 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12907 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12907

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12907
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12907 (61 / 100) 164 (17 / (100 * 12907)) (26 / (10 * 12907)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12907 (61 / 100) 164 (17 / (100 * 12907)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (453984671 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (140694097 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (898607089 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12907 / 12907 * (61 / 100)) ^ 4 * inverseRadius8 (12907 - 1) /
            envelopeGap 12907 (61 / 100) 164 (17 / (100 * 12907)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12907

namespace BstLean.Part266.Row12907
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12907 164 ≤ (880230869 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12907 164 ≤ (1468299549 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (352906343 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12907 164 ≤ (1746400331 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12907 164 ≤ (1242530463 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12907 164 ≤ (14187157 / 3125000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (453984671 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (453984671 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (140694097 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (898607089 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3629207 / 1000000000) : ℝ) ≤ √(17 / (100 * 12907) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12907) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (532672901 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18754605901 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12907) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12907) ≤ (109569503 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12907) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12907 * (164 : ℝ) ^ 2 + 26 / (10 * 12907) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12907) : ℝ)) (tA 12907 * 164 ^ 2 + 26 / (10 * 12907)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3629207 / 1000000000))) * ((453984671 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3629207 / 1000000000)) ^ 3) * ((140694097 / 100000000000000000000000))) + ((898607089 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3629207 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12907) : ℝ)) d.D d.V d.P (√(tA 12907) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3629207 / 1000000000)) ^ 2 * (((532672901 / 250000000000000)) * ((18754605901 / 500000000000000000)))) + ((898607089 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12907) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3629207 / 1000000000)) * ((453984671 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12907) : ℝ)) (tA 12907 * 164 ^ 2 + 26 / (10 * 12907)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((453984671 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3629207 / 1000000000)) ^ 2) * ((140694097 / 100000000000000000000000)) + ((898607089 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12907) : ℝ)) (√(26 / (10 * 12907) : ℝ)) d.D d.V d.P (√(tA 12907) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3629207 / 1000000000)) * (((532672901 / 250000000000000)) * ((18754605901 / 500000000000000000))) + ((898607089 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12907) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((453984671 / 100000000000000000000) : ℝ) + ((898607089 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12907

namespace BstLean.Part266.Row12907
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12907 164 ∧
    0 ≤ (tableEnvelope C).f1 12907 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12907 164 ∧
    0 ≤ (tableEnvelope C).w1 12907 164 ∧ 0 ≤ (tableEnvelope C).w2 12907 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12907 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12907 164 ∧ 0 ≤ d.f1 12907 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12907 164 ∧ 0 ≤ d.w1 12907 164 ∧ 0 ≤ d.w2 12907 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12907 ≤ 2 * (228 / 100 : ℝ) / 12907 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12907 ≤ 2 * (370 / 100 : ℝ) / 12907 := by
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
    (completeRAData (tableEnvelope C) 12907 164).locationBound 12907 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12907 164).energyBound 12907 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12907 164) (d.f1 12907 164) d.f2 ≤
      32 * (((880230869 / 200000000000000000) : ℝ) + (1468299549 / 1000000000000000000) + (352906343 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12907 164) (d.w1 12907 164)
      (d.w2 12907 164) ≤
      32 * (((1746400331 / 100000000000000000000) : ℝ) + (1242530463 / 100000000000000000000) + (14187157 / 3125000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12907 164) (d.f1 12907 164) d.f2 ≤
      ((880230869 / 200000000000000000) : ℝ) ^ 2 + 2 * ((880230869 / 200000000000000000)) * ((1468299549 / 1000000000000000000)) * (126 / 100) +
      2 * (((1468299549 / 1000000000000000000)) ^ 2 + 2 * ((880230869 / 200000000000000000)) * ((352906343 / 1000000000000000000))) +
      6 * ((1468299549 / 1000000000000000000)) * ((352906343 / 1000000000000000000)) * (126 / 100) + 8 * ((352906343 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12907 164) (d.f1 12907 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12907 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12907 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12907 164) (d.f1 12907 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12907 164) (d.w1 12907 164) (d.w2 12907 164)
  have hwexpr0 : 0 ≤ d.w0 12907 164 + d.w1 12907 164 * √(π / 2) +
      2 * d.w2 12907 164 + energyR16 12907 *
      radiusPolynomialRoot16 (d.w0 12907 164) (d.w1 12907 164) (d.w2 12907 164) := by
    positivity
  constructor
  · change (12907 : ℝ) ^ 8 * (mA 12907 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12907 164) (d.f1 12907 164) d.f2 + locationR16 12907 *
        radiusPolynomialRoot16 (d.f0 12907 164) (d.f1 12907 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12907 : ℝ) ^ 8 * (mA 12907 : ℝ) ^ 8 *
        ((((880230869 / 200000000000000000) : ℝ) ^ 2 + 2 * ((880230869 / 200000000000000000)) * ((1468299549 / 1000000000000000000)) * (126 / 100) +
          2 * (((1468299549 / 1000000000000000000)) ^ 2 + 2 * ((880230869 / 200000000000000000)) * ((352906343 / 1000000000000000000))) +
          6 * ((1468299549 / 1000000000000000000)) * ((352906343 / 1000000000000000000)) * (126 / 100) + 8 * ((352906343 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12907) *
          (32 * (((880230869 / 200000000000000000) : ℝ) + (1468299549 / 1000000000000000000) + (352906343 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12907 : ℝ) ^ 16 *
      (d.w0 12907 164 + d.w1 12907 164 * √(π / 2) + 2 * d.w2 12907 164 +
        energyR16 12907 * radiusPolynomialRoot16 (d.w0 12907 164) (d.w1 12907 164)
          (d.w2 12907 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12907 : ℝ) ^ 16 *
        (((1746400331 / 100000000000000000000) : ℝ) + ((1242530463 / 100000000000000000000)) * (126 / 100) + 2 * ((14187157 / 3125000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12907) *
          (32 * (((1746400331 / 100000000000000000000) : ℝ) + (1242530463 / 100000000000000000000) + (14187157 / 3125000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12907

/-! A coarse bound on the actual paper statistics constant at dimension 12908. -/
namespace BstLean.Part266.Row12908
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12906 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12906 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12906 128 ≤ (13160 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13160 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12908) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12908 : ℕ))
    (by norm_num : (12908 : ℕ) ≤ 16384)
  have ht : paperTail256 12908 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12908 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12908 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12908 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12908 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12908 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12906 128 * √(2 / (12908 : ℝ)) *
      (√(12908 : ℝ) + paperT0 12908 + paperTail256 12908) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12908 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12908 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12908 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12906 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12906 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12908 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12908

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12908
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12908 (61 / 100) 164 (17 / (100 * 12908)) (26 / (10 * 12908)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12908 (61 / 100) 164 (17 / (100 * 12908)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (226939581 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1406505013 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4490224981 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12908 / 12908 * (61 / 100)) ^ 4 * inverseRadius8 (12908 - 1) /
            envelopeGap 12908 (61 / 100) 164 (17 / (100 * 12908)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12908

namespace BstLean.Part266.Row12908
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12908 164 ≤ (2200151697 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12908 164 ≤ (367003877 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (176419017 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12908 164 ≤ (1745994751 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12908 164 ≤ (155280229 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 12908 164 ≤ (56735439 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (226939581 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (226939581 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1406505013 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4490224981 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1814533 / 500000000) : ℝ) ≤ √(17 / (100 * 12908) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12908) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (532610999 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1875170001 / 50000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12908) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12908) ≤ (54780507 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12908) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12908 * (164 : ℝ) ^ 2 + 26 / (10 * 12908) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12908) : ℝ)) (tA 12908 * 164 ^ 2 + 26 / (10 * 12908)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1814533 / 500000000))) * ((226939581 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1814533 / 500000000)) ^ 3) * ((1406505013 / 1000000000000000000000000))) + ((4490224981 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1814533 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12908) : ℝ)) d.D d.V d.P (√(tA 12908) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1814533 / 500000000)) ^ 2 * (((532610999 / 250000000000000)) * ((1875170001 / 50000000000000000)))) + ((4490224981 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12908) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1814533 / 500000000)) * ((226939581 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12908) : ℝ)) (tA 12908 * 164 ^ 2 + 26 / (10 * 12908)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((226939581 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1814533 / 500000000)) ^ 2) * ((1406505013 / 1000000000000000000000000)) + ((4490224981 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12908) : ℝ)) (√(26 / (10 * 12908) : ℝ)) d.D d.V d.P (√(tA 12908) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1814533 / 500000000)) * (((532610999 / 250000000000000)) * ((1875170001 / 50000000000000000))) + ((4490224981 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12908) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((226939581 / 50000000000000000000) : ℝ) + ((4490224981 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12908

namespace BstLean.Part266.Row12908
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12908 164 ∧
    0 ≤ (tableEnvelope C).f1 12908 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12908 164 ∧
    0 ≤ (tableEnvelope C).w1 12908 164 ∧ 0 ≤ (tableEnvelope C).w2 12908 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12908 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12908 164 ∧ 0 ≤ d.f1 12908 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12908 164 ∧ 0 ≤ d.w1 12908 164 ∧ 0 ≤ d.w2 12908 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12908 ≤ 2 * (228 / 100 : ℝ) / 12908 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12908 ≤ 2 * (370 / 100 : ℝ) / 12908 := by
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
    (completeRAData (tableEnvelope C) 12908 164).locationBound 12908 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12908 164).energyBound 12908 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12908 164) (d.f1 12908 164) d.f2 ≤
      32 * (((2200151697 / 500000000000000000) : ℝ) + (367003877 / 250000000000000000) + (176419017 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12908 164) (d.w1 12908 164)
      (d.w2 12908 164) ≤
      32 * (((1745994751 / 100000000000000000000) : ℝ) + (155280229 / 12500000000000000000) + (56735439 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12908 164) (d.f1 12908 164) d.f2 ≤
      ((2200151697 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2200151697 / 500000000000000000)) * ((367003877 / 250000000000000000)) * (126 / 100) +
      2 * (((367003877 / 250000000000000000)) ^ 2 + 2 * ((2200151697 / 500000000000000000)) * ((176419017 / 500000000000000000))) +
      6 * ((367003877 / 250000000000000000)) * ((176419017 / 500000000000000000)) * (126 / 100) + 8 * ((176419017 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12908 164) (d.f1 12908 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12908 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12908 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12908 164) (d.f1 12908 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12908 164) (d.w1 12908 164) (d.w2 12908 164)
  have hwexpr0 : 0 ≤ d.w0 12908 164 + d.w1 12908 164 * √(π / 2) +
      2 * d.w2 12908 164 + energyR16 12908 *
      radiusPolynomialRoot16 (d.w0 12908 164) (d.w1 12908 164) (d.w2 12908 164) := by
    positivity
  constructor
  · change (12908 : ℝ) ^ 8 * (mA 12908 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12908 164) (d.f1 12908 164) d.f2 + locationR16 12908 *
        radiusPolynomialRoot16 (d.f0 12908 164) (d.f1 12908 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12908 : ℝ) ^ 8 * (mA 12908 : ℝ) ^ 8 *
        ((((2200151697 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2200151697 / 500000000000000000)) * ((367003877 / 250000000000000000)) * (126 / 100) +
          2 * (((367003877 / 250000000000000000)) ^ 2 + 2 * ((2200151697 / 500000000000000000)) * ((176419017 / 500000000000000000))) +
          6 * ((367003877 / 250000000000000000)) * ((176419017 / 500000000000000000)) * (126 / 100) + 8 * ((176419017 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12908) *
          (32 * (((2200151697 / 500000000000000000) : ℝ) + (367003877 / 250000000000000000) + (176419017 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12908 : ℝ) ^ 16 *
      (d.w0 12908 164 + d.w1 12908 164 * √(π / 2) + 2 * d.w2 12908 164 +
        energyR16 12908 * radiusPolynomialRoot16 (d.w0 12908 164) (d.w1 12908 164)
          (d.w2 12908 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12908 : ℝ) ^ 16 *
        (((1745994751 / 100000000000000000000) : ℝ) + ((155280229 / 12500000000000000000)) * (126 / 100) + 2 * ((56735439 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12908) *
          (32 * (((1745994751 / 100000000000000000000) : ℝ) + (155280229 / 12500000000000000000) + (56735439 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12908

/-! A coarse bound on the actual paper statistics constant at dimension 12909. -/
namespace BstLean.Part266.Row12909
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12907 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12907 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12907 128 ≤ (13161 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13161 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12909) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12909 : ℕ))
    (by norm_num : (12909 : ℕ) ≤ 16384)
  have ht : paperTail256 12909 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12909 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12909 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12909 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12909 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12909 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12907 128 * √(2 / (12909 : ℝ)) *
      (√(12909 : ℝ) + paperT0 12909 + paperTail256 12909) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12909 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12909 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12909 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12907 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12907 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12909 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12909

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12909
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12909 (61 / 100) 164 (17 / (100 * 12909)) (26 / (10 * 12909)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12909 (61 / 100) 164 (17 / (100 * 12909)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (90754737 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (703034613 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4487416497 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12909 / 12909 * (61 / 100)) ^ 4 * inverseRadius8 (12909 - 1) /
            envelopeGap 12909 (61 / 100) 164 (17 / (100 * 12909)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12909

namespace BstLean.Part266.Row12909
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12909 164 ≤ (2199724617 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12909 164 ≤ (1467730749 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (352769647 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12909 164 ≤ (1745588597 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12909 164 ≤ (620976477 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12909 164 ≤ (28361127 / 6250000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (90754737 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (90754737 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (703034613 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4487416497 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1814463 / 500000000) : ℝ) ≤ √(17 / (100 * 12909) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12909) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (426039287 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37497589603 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12909) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12909) ≤ (109552527 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12909) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12909 * (164 : ℝ) ^ 2 + 26 / (10 * 12909) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12909) : ℝ)) (tA 12909 * 164 ^ 2 + 26 / (10 * 12909)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1814463 / 500000000))) * ((90754737 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1814463 / 500000000)) ^ 3) * ((703034613 / 500000000000000000000000))) + ((4487416497 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1814463 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12909) : ℝ)) d.D d.V d.P (√(tA 12909) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1814463 / 500000000)) ^ 2 * (((426039287 / 200000000000000)) * ((37497589603 / 1000000000000000000)))) + ((4487416497 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12909) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1814463 / 500000000)) * ((90754737 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12909) : ℝ)) (tA 12909 * 164 ^ 2 + 26 / (10 * 12909)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((90754737 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1814463 / 500000000)) ^ 2) * ((703034613 / 500000000000000000000000)) + ((4487416497 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12909) : ℝ)) (√(26 / (10 * 12909) : ℝ)) d.D d.V d.P (√(tA 12909) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1814463 / 500000000)) * (((426039287 / 200000000000000)) * ((37497589603 / 1000000000000000000))) + ((4487416497 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12909) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((90754737 / 20000000000000000000) : ℝ) + ((4487416497 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12909

namespace BstLean.Part266.Row12909
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12909 164 ∧
    0 ≤ (tableEnvelope C).f1 12909 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12909 164 ∧
    0 ≤ (tableEnvelope C).w1 12909 164 ∧ 0 ≤ (tableEnvelope C).w2 12909 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12909 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12909 164 ∧ 0 ≤ d.f1 12909 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12909 164 ∧ 0 ≤ d.w1 12909 164 ∧ 0 ≤ d.w2 12909 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12909 ≤ 2 * (228 / 100 : ℝ) / 12909 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12909 ≤ 2 * (370 / 100 : ℝ) / 12909 := by
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
    (completeRAData (tableEnvelope C) 12909 164).locationBound 12909 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12909 164).energyBound 12909 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12909 164) (d.f1 12909 164) d.f2 ≤
      32 * (((2199724617 / 500000000000000000) : ℝ) + (1467730749 / 1000000000000000000) + (352769647 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12909 164) (d.w1 12909 164)
      (d.w2 12909 164) ≤
      32 * (((1745588597 / 100000000000000000000) : ℝ) + (620976477 / 50000000000000000000) + (28361127 / 6250000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12909 164) (d.f1 12909 164) d.f2 ≤
      ((2199724617 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2199724617 / 500000000000000000)) * ((1467730749 / 1000000000000000000)) * (126 / 100) +
      2 * (((1467730749 / 1000000000000000000)) ^ 2 + 2 * ((2199724617 / 500000000000000000)) * ((352769647 / 1000000000000000000))) +
      6 * ((1467730749 / 1000000000000000000)) * ((352769647 / 1000000000000000000)) * (126 / 100) + 8 * ((352769647 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12909 164) (d.f1 12909 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12909 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12909 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12909 164) (d.f1 12909 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12909 164) (d.w1 12909 164) (d.w2 12909 164)
  have hwexpr0 : 0 ≤ d.w0 12909 164 + d.w1 12909 164 * √(π / 2) +
      2 * d.w2 12909 164 + energyR16 12909 *
      radiusPolynomialRoot16 (d.w0 12909 164) (d.w1 12909 164) (d.w2 12909 164) := by
    positivity
  constructor
  · change (12909 : ℝ) ^ 8 * (mA 12909 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12909 164) (d.f1 12909 164) d.f2 + locationR16 12909 *
        radiusPolynomialRoot16 (d.f0 12909 164) (d.f1 12909 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12909 : ℝ) ^ 8 * (mA 12909 : ℝ) ^ 8 *
        ((((2199724617 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2199724617 / 500000000000000000)) * ((1467730749 / 1000000000000000000)) * (126 / 100) +
          2 * (((1467730749 / 1000000000000000000)) ^ 2 + 2 * ((2199724617 / 500000000000000000)) * ((352769647 / 1000000000000000000))) +
          6 * ((1467730749 / 1000000000000000000)) * ((352769647 / 1000000000000000000)) * (126 / 100) + 8 * ((352769647 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12909) *
          (32 * (((2199724617 / 500000000000000000) : ℝ) + (1467730749 / 1000000000000000000) + (352769647 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12909 : ℝ) ^ 16 *
      (d.w0 12909 164 + d.w1 12909 164 * √(π / 2) + 2 * d.w2 12909 164 +
        energyR16 12909 * radiusPolynomialRoot16 (d.w0 12909 164) (d.w1 12909 164)
          (d.w2 12909 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12909 : ℝ) ^ 16 *
        (((1745588597 / 100000000000000000000) : ℝ) + ((620976477 / 50000000000000000000)) * (126 / 100) + 2 * ((28361127 / 6250000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12909) *
          (32 * (((1745588597 / 100000000000000000000) : ℝ) + (620976477 / 50000000000000000000) + (28361127 / 6250000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12909

/-! A coarse bound on the actual paper statistics constant at dimension 12910. -/
namespace BstLean.Part266.Row12910
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12908 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12908 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12908 128 ≤ (13162 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13162 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12910) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12910 : ℕ))
    (by norm_num : (12910 : ℕ) ≤ 16384)
  have ht : paperTail256 12910 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12910 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12910 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12910 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12910 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12910 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12908 128 * √(2 / (12910 : ℝ)) *
      (√(12910 : ℝ) + paperT0 12910 + paperTail256 12910) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12910 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12910 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12910 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12908 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12908 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12910 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12910

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12910
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12910 (61 / 100) 164 (17 / (100 * 12910)) (26 / (10 * 12910)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12910 (61 / 100) 164 (17 / (100 * 12910)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (5670853 / 1250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1405633607 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (448460999 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12910 / 12910 * (61 / 100)) ^ 4 * inverseRadius8 (12910 - 1) /
            envelopeGap 12910 (61 / 100) 164 (17 / (100 * 12910)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12910

namespace BstLean.Part266.Row12910
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12910 164 ≤ (4398598859 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12910 164 ≤ (1467446887 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (352701377 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12910 164 ≤ (174518329 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12910 164 ≤ (1212563 / 97656250000000000)
  w2 : (tableEnvelope C).w2 12910 164 ≤ (90734517 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (5670853 / 1250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (5670853 / 1250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1405633607 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (448460999 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((725757 / 200000000) : ℝ) ≤ √(17 / (100 * 12910) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12910) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (53248723 / 25000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18745890263 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12910) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12910) ≤ (109544041 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12910) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12910 * (164 : ℝ) ^ 2 + 26 / (10 * 12910) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12910) : ℝ)) (tA 12910 * 164 ^ 2 + 26 / (10 * 12910)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((725757 / 200000000))) * ((5670853 / 1250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((725757 / 200000000)) ^ 3) * ((1405633607 / 1000000000000000000000000))) + ((448460999 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((725757 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12910) : ℝ)) d.D d.V d.P (√(tA 12910) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((725757 / 200000000)) ^ 2 * (((53248723 / 25000000000000)) * ((18745890263 / 500000000000000000)))) + ((448460999 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12910) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((725757 / 200000000)) * ((5670853 / 1250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12910) : ℝ)) (tA 12910 * 164 ^ 2 + 26 / (10 * 12910)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((5670853 / 1250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((725757 / 200000000)) ^ 2) * ((1405633607 / 1000000000000000000000000)) + ((448460999 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12910) : ℝ)) (√(26 / (10 * 12910) : ℝ)) d.D d.V d.P (√(tA 12910) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((725757 / 200000000)) * (((53248723 / 25000000000000)) * ((18745890263 / 500000000000000000))) + ((448460999 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12910) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((5670853 / 1250000000000000000) : ℝ) + ((448460999 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12910

namespace BstLean.Part266.Row12910
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12910 164 ∧
    0 ≤ (tableEnvelope C).f1 12910 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12910 164 ∧
    0 ≤ (tableEnvelope C).w1 12910 164 ∧ 0 ≤ (tableEnvelope C).w2 12910 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12910 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12910 164 ∧ 0 ≤ d.f1 12910 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12910 164 ∧ 0 ≤ d.w1 12910 164 ∧ 0 ≤ d.w2 12910 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12910 ≤ 2 * (228 / 100 : ℝ) / 12910 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12910 ≤ 2 * (370 / 100 : ℝ) / 12910 := by
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
    (completeRAData (tableEnvelope C) 12910 164).locationBound 12910 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12910 164).energyBound 12910 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12910 164) (d.f1 12910 164) d.f2 ≤
      32 * (((4398598859 / 1000000000000000000) : ℝ) + (1467446887 / 1000000000000000000) + (352701377 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12910 164) (d.w1 12910 164)
      (d.w2 12910 164) ≤
      32 * (((174518329 / 10000000000000000000) : ℝ) + (1212563 / 97656250000000000) + (90734517 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12910 164) (d.f1 12910 164) d.f2 ≤
      ((4398598859 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4398598859 / 1000000000000000000)) * ((1467446887 / 1000000000000000000)) * (126 / 100) +
      2 * (((1467446887 / 1000000000000000000)) ^ 2 + 2 * ((4398598859 / 1000000000000000000)) * ((352701377 / 1000000000000000000))) +
      6 * ((1467446887 / 1000000000000000000)) * ((352701377 / 1000000000000000000)) * (126 / 100) + 8 * ((352701377 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12910 164) (d.f1 12910 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12910 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12910 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12910 164) (d.f1 12910 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12910 164) (d.w1 12910 164) (d.w2 12910 164)
  have hwexpr0 : 0 ≤ d.w0 12910 164 + d.w1 12910 164 * √(π / 2) +
      2 * d.w2 12910 164 + energyR16 12910 *
      radiusPolynomialRoot16 (d.w0 12910 164) (d.w1 12910 164) (d.w2 12910 164) := by
    positivity
  constructor
  · change (12910 : ℝ) ^ 8 * (mA 12910 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12910 164) (d.f1 12910 164) d.f2 + locationR16 12910 *
        radiusPolynomialRoot16 (d.f0 12910 164) (d.f1 12910 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12910 : ℝ) ^ 8 * (mA 12910 : ℝ) ^ 8 *
        ((((4398598859 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4398598859 / 1000000000000000000)) * ((1467446887 / 1000000000000000000)) * (126 / 100) +
          2 * (((1467446887 / 1000000000000000000)) ^ 2 + 2 * ((4398598859 / 1000000000000000000)) * ((352701377 / 1000000000000000000))) +
          6 * ((1467446887 / 1000000000000000000)) * ((352701377 / 1000000000000000000)) * (126 / 100) + 8 * ((352701377 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12910) *
          (32 * (((4398598859 / 1000000000000000000) : ℝ) + (1467446887 / 1000000000000000000) + (352701377 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12910 : ℝ) ^ 16 *
      (d.w0 12910 164 + d.w1 12910 164 * √(π / 2) + 2 * d.w2 12910 164 +
        energyR16 12910 * radiusPolynomialRoot16 (d.w0 12910 164) (d.w1 12910 164)
          (d.w2 12910 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12910 : ℝ) ^ 16 *
        (((174518329 / 10000000000000000000) : ℝ) + ((1212563 / 97656250000000000)) * (126 / 100) + 2 * ((90734517 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12910) *
          (32 * (((174518329 / 10000000000000000000) : ℝ) + (1212563 / 97656250000000000) + (90734517 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12910

/-! A coarse bound on the actual paper statistics constant at dimension 12911. -/
namespace BstLean.Part266.Row12911
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12909 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12909 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12909 128 ≤ (13163 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13163 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12911) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12911 : ℕ))
    (by norm_num : (12911 : ℕ) ≤ 16384)
  have ht : paperTail256 12911 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12911 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12911 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12911 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12911 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12911 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12909 128 * √(2 / (12911 : ℝ)) *
      (√(12911 : ℝ) + paperT0 12911 + paperTail256 12911) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12911 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12911 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12911 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12909 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12909 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12911 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12911

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12911
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12911 (61 / 100) 164 (17 / (100 * 12911)) (26 / (10 * 12911)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12911 (61 / 100) 164 (17 / (100 * 12911)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (453562829 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (351299539 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (224090273 / 50000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12911 / 12911 * (61 / 100)) ^ 4 * inverseRadius8 (12911 - 1) /
            envelopeGap 12911 (61 / 100) 164 (17 / (100 * 12911)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12911

namespace BstLean.Part266.Row12911
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12911 164 ≤ (4397745273 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12911 164 ≤ (366790577 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (35263303 / 100000000000000000)
  w0 : (tableEnvelope C).w0 12911 164 ≤ (174477741 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12911 164 ≤ (77585989 / 6250000000000000000)
  w2 : (tableEnvelope C).w2 12911 164 ≤ (453567171 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (453562829 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (453562829 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (351299539 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (224090273 / 50000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((725729 / 200000000) : ℝ) ≤ √(17 / (100 * 12911) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12911) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (133106341 / 62500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3748597279 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12911) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12911) ≤ (27383889 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12911) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12911 * (164 : ℝ) ^ 2 + 26 / (10 * 12911) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12911) : ℝ)) (tA 12911 * 164 ^ 2 + 26 / (10 * 12911)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((725729 / 200000000))) * ((453562829 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((725729 / 200000000)) ^ 3) * ((351299539 / 250000000000000000000000))) + ((224090273 / 50000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((725729 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12911) : ℝ)) d.D d.V d.P (√(tA 12911) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((725729 / 200000000)) ^ 2 * (((133106341 / 62500000000000)) * ((3748597279 / 100000000000000000)))) + ((224090273 / 50000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12911) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((725729 / 200000000)) * ((453562829 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12911) : ℝ)) (tA 12911 * 164 ^ 2 + 26 / (10 * 12911)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((453562829 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((725729 / 200000000)) ^ 2) * ((351299539 / 250000000000000000000000)) + ((224090273 / 50000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12911) : ℝ)) (√(26 / (10 * 12911) : ℝ)) d.D d.V d.P (√(tA 12911) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((725729 / 200000000)) * (((133106341 / 62500000000000)) * ((3748597279 / 100000000000000000))) + ((224090273 / 50000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12911) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((453562829 / 100000000000000000000) : ℝ) + ((224090273 / 50000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12911

namespace BstLean.Part266.Row12911
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12911 164 ∧
    0 ≤ (tableEnvelope C).f1 12911 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12911 164 ∧
    0 ≤ (tableEnvelope C).w1 12911 164 ∧ 0 ≤ (tableEnvelope C).w2 12911 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12911 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12911 164 ∧ 0 ≤ d.f1 12911 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12911 164 ∧ 0 ≤ d.w1 12911 164 ∧ 0 ≤ d.w2 12911 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12911 ≤ 2 * (228 / 100 : ℝ) / 12911 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12911 ≤ 2 * (370 / 100 : ℝ) / 12911 := by
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
    (completeRAData (tableEnvelope C) 12911 164).locationBound 12911 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12911 164).energyBound 12911 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12911 164) (d.f1 12911 164) d.f2 ≤
      32 * (((4397745273 / 1000000000000000000) : ℝ) + (366790577 / 250000000000000000) + (35263303 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12911 164) (d.w1 12911 164)
      (d.w2 12911 164) ≤
      32 * (((174477741 / 10000000000000000000) : ℝ) + (77585989 / 6250000000000000000) + (453567171 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12911 164) (d.f1 12911 164) d.f2 ≤
      ((4397745273 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4397745273 / 1000000000000000000)) * ((366790577 / 250000000000000000)) * (126 / 100) +
      2 * (((366790577 / 250000000000000000)) ^ 2 + 2 * ((4397745273 / 1000000000000000000)) * ((35263303 / 100000000000000000))) +
      6 * ((366790577 / 250000000000000000)) * ((35263303 / 100000000000000000)) * (126 / 100) + 8 * ((35263303 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12911 164) (d.f1 12911 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12911 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12911 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12911 164) (d.f1 12911 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12911 164) (d.w1 12911 164) (d.w2 12911 164)
  have hwexpr0 : 0 ≤ d.w0 12911 164 + d.w1 12911 164 * √(π / 2) +
      2 * d.w2 12911 164 + energyR16 12911 *
      radiusPolynomialRoot16 (d.w0 12911 164) (d.w1 12911 164) (d.w2 12911 164) := by
    positivity
  constructor
  · change (12911 : ℝ) ^ 8 * (mA 12911 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12911 164) (d.f1 12911 164) d.f2 + locationR16 12911 *
        radiusPolynomialRoot16 (d.f0 12911 164) (d.f1 12911 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12911 : ℝ) ^ 8 * (mA 12911 : ℝ) ^ 8 *
        ((((4397745273 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4397745273 / 1000000000000000000)) * ((366790577 / 250000000000000000)) * (126 / 100) +
          2 * (((366790577 / 250000000000000000)) ^ 2 + 2 * ((4397745273 / 1000000000000000000)) * ((35263303 / 100000000000000000))) +
          6 * ((366790577 / 250000000000000000)) * ((35263303 / 100000000000000000)) * (126 / 100) + 8 * ((35263303 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12911) *
          (32 * (((4397745273 / 1000000000000000000) : ℝ) + (366790577 / 250000000000000000) + (35263303 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12911 : ℝ) ^ 16 *
      (d.w0 12911 164 + d.w1 12911 164 * √(π / 2) + 2 * d.w2 12911 164 +
        energyR16 12911 * radiusPolynomialRoot16 (d.w0 12911 164) (d.w1 12911 164)
          (d.w2 12911 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12911 : ℝ) ^ 16 *
        (((174477741 / 10000000000000000000) : ℝ) + ((77585989 / 6250000000000000000)) * (126 / 100) + 2 * ((453567171 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12911) *
          (32 * (((174477741 / 10000000000000000000) : ℝ) + (77585989 / 6250000000000000000) + (453567171 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12911

/-! A coarse bound on the actual paper statistics constant at dimension 12912. -/
namespace BstLean.Part266.Row12912
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12910 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12910 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12910 128 ≤ (13164 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13164 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12912) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12912 : ℕ))
    (by norm_num : (12912 : ℕ) ≤ 16384)
  have ht : paperTail256 12912 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12912 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12912 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12912 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12912 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12912 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12910 128 * √(2 / (12912 : ℝ)) *
      (√(12912 : ℝ) + paperT0 12912 + paperTail256 12912) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12912 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12912 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12912 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12910 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12910 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12912 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12912

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12912
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12912 (61 / 100) 164 (17 / (100 * 12912)) (26 / (10 * 12912)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12912 (61 / 100) 164 (17 / (100 * 12912)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (9069149 / 2000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (11238103 / 8000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (895800581 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12912 / 12912 * (61 / 100)) ^ 4 * inverseRadius8 (12912 - 1) /
            envelopeGap 12912 (61 / 100) 164 (17 / (100 * 12912)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12912

namespace BstLean.Part266.Row12912
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12912 164 ≤ (1099223869 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12912 164 ≤ (1466878629 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (352564801 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12912 164 ≤ (1744372379 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12912 164 ≤ (1241087573 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12912 164 ≤ (453461789 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (9069149 / 2000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (9069149 / 2000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (11238103 / 8000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (895800581 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((453563 / 125000000) : ℝ) ≤ √(17 / (100 * 12912) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12912) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2129454039 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18740083211 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12912) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12912) ≤ (109527073 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12912) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12912 * (164 : ℝ) ^ 2 + 26 / (10 * 12912) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12912) : ℝ)) (tA 12912 * 164 ^ 2 + 26 / (10 * 12912)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((453563 / 125000000))) * ((9069149 / 2000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((453563 / 125000000)) ^ 3) * ((11238103 / 8000000000000000000000))) + ((895800581 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((453563 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12912) : ℝ)) d.D d.V d.P (√(tA 12912) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((453563 / 125000000)) ^ 2 * (((2129454039 / 1000000000000000)) * ((18740083211 / 500000000000000000)))) + ((895800581 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12912) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((453563 / 125000000)) * ((9069149 / 2000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12912) : ℝ)) (tA 12912 * 164 ^ 2 + 26 / (10 * 12912)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((9069149 / 2000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((453563 / 125000000)) ^ 2) * ((11238103 / 8000000000000000000000)) + ((895800581 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12912) : ℝ)) (√(26 / (10 * 12912) : ℝ)) d.D d.V d.P (√(tA 12912) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((453563 / 125000000)) * (((2129454039 / 1000000000000000)) * ((18740083211 / 500000000000000000))) + ((895800581 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12912) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((9069149 / 2000000000000000000) : ℝ) + ((895800581 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12912

namespace BstLean.Part266.Row12912
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12912 164 ∧
    0 ≤ (tableEnvelope C).f1 12912 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12912 164 ∧
    0 ≤ (tableEnvelope C).w1 12912 164 ∧ 0 ≤ (tableEnvelope C).w2 12912 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12912 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12912 164 ∧ 0 ≤ d.f1 12912 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12912 164 ∧ 0 ≤ d.w1 12912 164 ∧ 0 ≤ d.w2 12912 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12912 ≤ 2 * (228 / 100 : ℝ) / 12912 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12912 ≤ 2 * (370 / 100 : ℝ) / 12912 := by
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
    (completeRAData (tableEnvelope C) 12912 164).locationBound 12912 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12912 164).energyBound 12912 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12912 164) (d.f1 12912 164) d.f2 ≤
      32 * (((1099223869 / 250000000000000000) : ℝ) + (1466878629 / 1000000000000000000) + (352564801 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12912 164) (d.w1 12912 164)
      (d.w2 12912 164) ≤
      32 * (((1744372379 / 100000000000000000000) : ℝ) + (1241087573 / 100000000000000000000) + (453461789 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12912 164) (d.f1 12912 164) d.f2 ≤
      ((1099223869 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1099223869 / 250000000000000000)) * ((1466878629 / 1000000000000000000)) * (126 / 100) +
      2 * (((1466878629 / 1000000000000000000)) ^ 2 + 2 * ((1099223869 / 250000000000000000)) * ((352564801 / 1000000000000000000))) +
      6 * ((1466878629 / 1000000000000000000)) * ((352564801 / 1000000000000000000)) * (126 / 100) + 8 * ((352564801 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12912 164) (d.f1 12912 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12912 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12912 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12912 164) (d.f1 12912 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12912 164) (d.w1 12912 164) (d.w2 12912 164)
  have hwexpr0 : 0 ≤ d.w0 12912 164 + d.w1 12912 164 * √(π / 2) +
      2 * d.w2 12912 164 + energyR16 12912 *
      radiusPolynomialRoot16 (d.w0 12912 164) (d.w1 12912 164) (d.w2 12912 164) := by
    positivity
  constructor
  · change (12912 : ℝ) ^ 8 * (mA 12912 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12912 164) (d.f1 12912 164) d.f2 + locationR16 12912 *
        radiusPolynomialRoot16 (d.f0 12912 164) (d.f1 12912 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12912 : ℝ) ^ 8 * (mA 12912 : ℝ) ^ 8 *
        ((((1099223869 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1099223869 / 250000000000000000)) * ((1466878629 / 1000000000000000000)) * (126 / 100) +
          2 * (((1466878629 / 1000000000000000000)) ^ 2 + 2 * ((1099223869 / 250000000000000000)) * ((352564801 / 1000000000000000000))) +
          6 * ((1466878629 / 1000000000000000000)) * ((352564801 / 1000000000000000000)) * (126 / 100) + 8 * ((352564801 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12912) *
          (32 * (((1099223869 / 250000000000000000) : ℝ) + (1466878629 / 1000000000000000000) + (352564801 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12912 : ℝ) ^ 16 *
      (d.w0 12912 164 + d.w1 12912 164 * √(π / 2) + 2 * d.w2 12912 164 +
        energyR16 12912 * radiusPolynomialRoot16 (d.w0 12912 164) (d.w1 12912 164)
          (d.w2 12912 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12912 : ℝ) ^ 16 *
        (((1744372379 / 100000000000000000000) : ℝ) + ((1241087573 / 100000000000000000000)) * (126 / 100) + 2 * ((453461789 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12912) *
          (32 * (((1744372379 / 100000000000000000000) : ℝ) + (1241087573 / 100000000000000000000) + (453461789 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12912

/-! A coarse bound on the actual paper statistics constant at dimension 12913. -/
namespace BstLean.Part266.Row12913
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12911 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12911 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12911 128 ≤ (13165 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13165 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12913) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12913 : ℕ))
    (by norm_num : (12913 : ℕ) ≤ 16384)
  have ht : paperTail256 12913 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12913 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12913 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12913 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12913 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12913 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12911 128 * √(2 / (12913 : ℝ)) *
      (√(12913 : ℝ) + paperT0 12913 + paperTail256 12913) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12913 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12913 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12913 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12911 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12911 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12913 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12913

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12913
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12913 (61 / 100) 164 (17 / (100 * 12913)) (26 / (10 * 12913)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12913 (61 / 100) 164 (17 / (100 * 12913)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (453352103 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (702163881 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4476202323 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12913 / 12913 * (61 / 100)) ^ 4 * inverseRadius8 (12913 - 1) /
            envelopeGap 12913 (61 / 100) 164 (17 / (100 * 12913)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12913

namespace BstLean.Part266.Row12913
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12913 164 ≤ (4396042467 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12913 164 ≤ (366648557 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (352496493 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12913 164 ≤ (1743966773 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12913 164 ≤ (1240799073 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12913 164 ≤ (11333911 / 2500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (453352103 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (453352103 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (702163881 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4476202323 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((907091 / 250000000) : ℝ) ≤ √(17 / (100 * 12913) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12913) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2129206667 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9368590349 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12913) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12913) ≤ (109518591 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12913) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12913 * (164 : ℝ) ^ 2 + 26 / (10 * 12913) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12913) : ℝ)) (tA 12913 * 164 ^ 2 + 26 / (10 * 12913)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((907091 / 250000000))) * ((453352103 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((907091 / 250000000)) ^ 3) * ((702163881 / 500000000000000000000000))) + ((4476202323 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((907091 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12913) : ℝ)) d.D d.V d.P (√(tA 12913) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((907091 / 250000000)) ^ 2 * (((2129206667 / 1000000000000000)) * ((9368590349 / 250000000000000000)))) + ((4476202323 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12913) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((907091 / 250000000)) * ((453352103 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12913) : ℝ)) (tA 12913 * 164 ^ 2 + 26 / (10 * 12913)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((453352103 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((907091 / 250000000)) ^ 2) * ((702163881 / 500000000000000000000000)) + ((4476202323 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12913) : ℝ)) (√(26 / (10 * 12913) : ℝ)) d.D d.V d.P (√(tA 12913) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((907091 / 250000000)) * (((2129206667 / 1000000000000000)) * ((9368590349 / 250000000000000000))) + ((4476202323 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12913) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((453352103 / 100000000000000000000) : ℝ) + ((4476202323 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12913

namespace BstLean.Part266.Row12913
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12913 164 ∧
    0 ≤ (tableEnvelope C).f1 12913 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12913 164 ∧
    0 ≤ (tableEnvelope C).w1 12913 164 ∧ 0 ≤ (tableEnvelope C).w2 12913 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12913 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12913 164 ∧ 0 ≤ d.f1 12913 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12913 164 ∧ 0 ≤ d.w1 12913 164 ∧ 0 ≤ d.w2 12913 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12913 ≤ 2 * (228 / 100 : ℝ) / 12913 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12913 ≤ 2 * (370 / 100 : ℝ) / 12913 := by
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
    (completeRAData (tableEnvelope C) 12913 164).locationBound 12913 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12913 164).energyBound 12913 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12913 164) (d.f1 12913 164) d.f2 ≤
      32 * (((4396042467 / 1000000000000000000) : ℝ) + (366648557 / 250000000000000000) + (352496493 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12913 164) (d.w1 12913 164)
      (d.w2 12913 164) ≤
      32 * (((1743966773 / 100000000000000000000) : ℝ) + (1240799073 / 100000000000000000000) + (11333911 / 2500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12913 164) (d.f1 12913 164) d.f2 ≤
      ((4396042467 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4396042467 / 1000000000000000000)) * ((366648557 / 250000000000000000)) * (126 / 100) +
      2 * (((366648557 / 250000000000000000)) ^ 2 + 2 * ((4396042467 / 1000000000000000000)) * ((352496493 / 1000000000000000000))) +
      6 * ((366648557 / 250000000000000000)) * ((352496493 / 1000000000000000000)) * (126 / 100) + 8 * ((352496493 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12913 164) (d.f1 12913 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12913 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12913 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12913 164) (d.f1 12913 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12913 164) (d.w1 12913 164) (d.w2 12913 164)
  have hwexpr0 : 0 ≤ d.w0 12913 164 + d.w1 12913 164 * √(π / 2) +
      2 * d.w2 12913 164 + energyR16 12913 *
      radiusPolynomialRoot16 (d.w0 12913 164) (d.w1 12913 164) (d.w2 12913 164) := by
    positivity
  constructor
  · change (12913 : ℝ) ^ 8 * (mA 12913 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12913 164) (d.f1 12913 164) d.f2 + locationR16 12913 *
        radiusPolynomialRoot16 (d.f0 12913 164) (d.f1 12913 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12913 : ℝ) ^ 8 * (mA 12913 : ℝ) ^ 8 *
        ((((4396042467 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4396042467 / 1000000000000000000)) * ((366648557 / 250000000000000000)) * (126 / 100) +
          2 * (((366648557 / 250000000000000000)) ^ 2 + 2 * ((4396042467 / 1000000000000000000)) * ((352496493 / 1000000000000000000))) +
          6 * ((366648557 / 250000000000000000)) * ((352496493 / 1000000000000000000)) * (126 / 100) + 8 * ((352496493 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12913) *
          (32 * (((4396042467 / 1000000000000000000) : ℝ) + (366648557 / 250000000000000000) + (352496493 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12913 : ℝ) ^ 16 *
      (d.w0 12913 164 + d.w1 12913 164 * √(π / 2) + 2 * d.w2 12913 164 +
        energyR16 12913 * radiusPolynomialRoot16 (d.w0 12913 164) (d.w1 12913 164)
          (d.w2 12913 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12913 : ℝ) ^ 16 *
        (((1743966773 / 100000000000000000000) : ℝ) + ((1240799073 / 100000000000000000000)) * (126 / 100) + 2 * ((11333911 / 2500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12913) *
          (32 * (((1743966773 / 100000000000000000000) : ℝ) + (1240799073 / 100000000000000000000) + (11333911 / 2500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12913

/-! A coarse bound on the actual paper statistics constant at dimension 12914. -/
namespace BstLean.Part266.Row12914
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12912 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12912 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12912 128 ≤ (13166 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13166 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12914) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12914 : ℕ))
    (by norm_num : (12914 : ℕ) ≤ 16384)
  have ht : paperTail256 12914 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12914 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12914 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12914 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12914 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12914 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12912 128 * √(2 / (12914 : ℝ)) *
      (√(12914 : ℝ) + paperT0 12914 + paperTail256 12914) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12914 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12914 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12914 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12912 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12912 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12914 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12914

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12914
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12914 (61 / 100) 164 (17 / (100 * 12914)) (26 / (10 * 12914)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12914 (61 / 100) 164 (17 / (100 * 12914)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (45324679 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1403892817 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4473403713 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12914 / 12914 * (61 / 100)) ^ 4 * inverseRadius8 (12914 - 1) /
            envelopeGap 12914 (61 / 100) 164 (17 / (100 * 12914)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12914

namespace BstLean.Part266.Row12914
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12914 164 ≤ (4395193243 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12914 164 ≤ (1466310729 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (70485661 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12914 164 ≤ (54486313 / 3125000000000000000)
  w1 : (tableEnvelope C).w1 12914 164 ≤ (1240511013 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12914 164 ≤ (113312781 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (45324679 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (45324679 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1403892817 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4473403713 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3628223 / 1000000000) : ℝ) ≤ √(17 / (100 * 12914) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12914) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2128959347 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (2341784857 / 62500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12914) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12914) ≤ (109510111 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12914) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12914 * (164 : ℝ) ^ 2 + 26 / (10 * 12914) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12914) : ℝ)) (tA 12914 * 164 ^ 2 + 26 / (10 * 12914)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3628223 / 1000000000))) * ((45324679 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3628223 / 1000000000)) ^ 3) * ((1403892817 / 1000000000000000000000000))) + ((4473403713 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3628223 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12914) : ℝ)) d.D d.V d.P (√(tA 12914) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3628223 / 1000000000)) ^ 2 * (((2128959347 / 1000000000000000)) * ((2341784857 / 62500000000000000)))) + ((4473403713 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12914) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3628223 / 1000000000)) * ((45324679 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12914) : ℝ)) (tA 12914 * 164 ^ 2 + 26 / (10 * 12914)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((45324679 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3628223 / 1000000000)) ^ 2) * ((1403892817 / 1000000000000000000000000)) + ((4473403713 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12914) : ℝ)) (√(26 / (10 * 12914) : ℝ)) d.D d.V d.P (√(tA 12914) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3628223 / 1000000000)) * (((2128959347 / 1000000000000000)) * ((2341784857 / 62500000000000000))) + ((4473403713 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12914) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((45324679 / 10000000000000000000) : ℝ) + ((4473403713 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12914

namespace BstLean.Part266.Row12914
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12914 164 ∧
    0 ≤ (tableEnvelope C).f1 12914 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12914 164 ∧
    0 ≤ (tableEnvelope C).w1 12914 164 ∧ 0 ≤ (tableEnvelope C).w2 12914 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12914 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12914 164 ∧ 0 ≤ d.f1 12914 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12914 164 ∧ 0 ≤ d.w1 12914 164 ∧ 0 ≤ d.w2 12914 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12914 ≤ 2 * (228 / 100 : ℝ) / 12914 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12914 ≤ 2 * (370 / 100 : ℝ) / 12914 := by
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
    (completeRAData (tableEnvelope C) 12914 164).locationBound 12914 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12914 164).energyBound 12914 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12914 164) (d.f1 12914 164) d.f2 ≤
      32 * (((4395193243 / 1000000000000000000) : ℝ) + (1466310729 / 1000000000000000000) + (70485661 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12914 164) (d.w1 12914 164)
      (d.w2 12914 164) ≤
      32 * (((54486313 / 3125000000000000000) : ℝ) + (1240511013 / 100000000000000000000) + (113312781 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12914 164) (d.f1 12914 164) d.f2 ≤
      ((4395193243 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4395193243 / 1000000000000000000)) * ((1466310729 / 1000000000000000000)) * (126 / 100) +
      2 * (((1466310729 / 1000000000000000000)) ^ 2 + 2 * ((4395193243 / 1000000000000000000)) * ((70485661 / 200000000000000000))) +
      6 * ((1466310729 / 1000000000000000000)) * ((70485661 / 200000000000000000)) * (126 / 100) + 8 * ((70485661 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12914 164) (d.f1 12914 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12914 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12914 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12914 164) (d.f1 12914 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12914 164) (d.w1 12914 164) (d.w2 12914 164)
  have hwexpr0 : 0 ≤ d.w0 12914 164 + d.w1 12914 164 * √(π / 2) +
      2 * d.w2 12914 164 + energyR16 12914 *
      radiusPolynomialRoot16 (d.w0 12914 164) (d.w1 12914 164) (d.w2 12914 164) := by
    positivity
  constructor
  · change (12914 : ℝ) ^ 8 * (mA 12914 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12914 164) (d.f1 12914 164) d.f2 + locationR16 12914 *
        radiusPolynomialRoot16 (d.f0 12914 164) (d.f1 12914 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12914 : ℝ) ^ 8 * (mA 12914 : ℝ) ^ 8 *
        ((((4395193243 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4395193243 / 1000000000000000000)) * ((1466310729 / 1000000000000000000)) * (126 / 100) +
          2 * (((1466310729 / 1000000000000000000)) ^ 2 + 2 * ((4395193243 / 1000000000000000000)) * ((70485661 / 200000000000000000))) +
          6 * ((1466310729 / 1000000000000000000)) * ((70485661 / 200000000000000000)) * (126 / 100) + 8 * ((70485661 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12914) *
          (32 * (((4395193243 / 1000000000000000000) : ℝ) + (1466310729 / 1000000000000000000) + (70485661 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12914 : ℝ) ^ 16 *
      (d.w0 12914 164 + d.w1 12914 164 * √(π / 2) + 2 * d.w2 12914 164 +
        energyR16 12914 * radiusPolynomialRoot16 (d.w0 12914 164) (d.w1 12914 164)
          (d.w2 12914 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12914 : ℝ) ^ 16 *
        (((54486313 / 3125000000000000000) : ℝ) + ((1240511013 / 100000000000000000000)) * (126 / 100) + 2 * ((113312781 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12914) *
          (32 * (((54486313 / 3125000000000000000) : ℝ) + (1240511013 / 100000000000000000000) + (113312781 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12914

/-! A coarse bound on the actual paper statistics constant at dimension 12915. -/
namespace BstLean.Part266.Row12915
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12913 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12913 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12913 128 ≤ (13167 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13167 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12915) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12915 : ℕ))
    (by norm_num : (12915 : ℕ) ≤ 16384)
  have ht : paperTail256 12915 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12915 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12915 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12915 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12915 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12915 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12913 128 * √(2 / (12915 : ℝ)) *
      (√(12915 : ℝ) + paperT0 12915 + paperTail256 12915) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12915 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12915 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12915 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12913 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12913 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12915 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12915

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12915
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12915 (61 / 100) 164 (17 / (100 * 12915)) (26 / (10 * 12915)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12915 (61 / 100) 164 (17 / (100 * 12915)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (453141509 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (35086451 / 25000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2235303537 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12915 / 12915 * (61 / 100)) ^ 4 * inverseRadius8 (12915 - 1) /
            envelopeGap 12915 (61 / 100) 164 (17 / (100 * 12915)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12915

namespace BstLean.Part266.Row12915
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12915 164 ≤ (4394340809 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12915 164 ≤ (1466026511 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (176180019 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12915 164 ≤ (435789171 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12915 164 ≤ (77513919 / 6250000000000000000)
  w2 : (tableEnvelope C).w2 12915 164 ≤ (5664323 / 1250000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (453141509 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (453141509 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (35086451 / 25000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2235303537 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3628083 / 1000000000) : ℝ) ≤ √(17 / (100 * 12915) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12915) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1064356037 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9365688843 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12915) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12915) ≤ (109501631 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12915) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12915 * (164 : ℝ) ^ 2 + 26 / (10 * 12915) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12915) : ℝ)) (tA 12915 * 164 ^ 2 + 26 / (10 * 12915)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3628083 / 1000000000))) * ((453141509 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3628083 / 1000000000)) ^ 3) * ((35086451 / 25000000000000000000000))) + ((2235303537 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3628083 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12915) : ℝ)) d.D d.V d.P (√(tA 12915) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3628083 / 1000000000)) ^ 2 * (((1064356037 / 500000000000000)) * ((9365688843 / 250000000000000000)))) + ((2235303537 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12915) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3628083 / 1000000000)) * ((453141509 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12915) : ℝ)) (tA 12915 * 164 ^ 2 + 26 / (10 * 12915)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((453141509 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3628083 / 1000000000)) ^ 2) * ((35086451 / 25000000000000000000000)) + ((2235303537 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12915) : ℝ)) (√(26 / (10 * 12915) : ℝ)) d.D d.V d.P (√(tA 12915) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3628083 / 1000000000)) * (((1064356037 / 500000000000000)) * ((9365688843 / 250000000000000000))) + ((2235303537 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12915) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((453141509 / 100000000000000000000) : ℝ) + ((2235303537 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12915

namespace BstLean.Part266.Row12915
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12915 164 ∧
    0 ≤ (tableEnvelope C).f1 12915 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12915 164 ∧
    0 ≤ (tableEnvelope C).w1 12915 164 ∧ 0 ≤ (tableEnvelope C).w2 12915 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12915 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12915 164 ∧ 0 ≤ d.f1 12915 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12915 164 ∧ 0 ≤ d.w1 12915 164 ∧ 0 ≤ d.w2 12915 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12915 ≤ 2 * (228 / 100 : ℝ) / 12915 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12915 ≤ 2 * (370 / 100 : ℝ) / 12915 := by
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
    (completeRAData (tableEnvelope C) 12915 164).locationBound 12915 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12915 164).energyBound 12915 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12915 164) (d.f1 12915 164) d.f2 ≤
      32 * (((4394340809 / 1000000000000000000) : ℝ) + (1466026511 / 1000000000000000000) + (176180019 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12915 164) (d.w1 12915 164)
      (d.w2 12915 164) ≤
      32 * (((435789171 / 25000000000000000000) : ℝ) + (77513919 / 6250000000000000000) + (5664323 / 1250000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12915 164) (d.f1 12915 164) d.f2 ≤
      ((4394340809 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4394340809 / 1000000000000000000)) * ((1466026511 / 1000000000000000000)) * (126 / 100) +
      2 * (((1466026511 / 1000000000000000000)) ^ 2 + 2 * ((4394340809 / 1000000000000000000)) * ((176180019 / 500000000000000000))) +
      6 * ((1466026511 / 1000000000000000000)) * ((176180019 / 500000000000000000)) * (126 / 100) + 8 * ((176180019 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12915 164) (d.f1 12915 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12915 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12915 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12915 164) (d.f1 12915 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12915 164) (d.w1 12915 164) (d.w2 12915 164)
  have hwexpr0 : 0 ≤ d.w0 12915 164 + d.w1 12915 164 * √(π / 2) +
      2 * d.w2 12915 164 + energyR16 12915 *
      radiusPolynomialRoot16 (d.w0 12915 164) (d.w1 12915 164) (d.w2 12915 164) := by
    positivity
  constructor
  · change (12915 : ℝ) ^ 8 * (mA 12915 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12915 164) (d.f1 12915 164) d.f2 + locationR16 12915 *
        radiusPolynomialRoot16 (d.f0 12915 164) (d.f1 12915 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12915 : ℝ) ^ 8 * (mA 12915 : ℝ) ^ 8 *
        ((((4394340809 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4394340809 / 1000000000000000000)) * ((1466026511 / 1000000000000000000)) * (126 / 100) +
          2 * (((1466026511 / 1000000000000000000)) ^ 2 + 2 * ((4394340809 / 1000000000000000000)) * ((176180019 / 500000000000000000))) +
          6 * ((1466026511 / 1000000000000000000)) * ((176180019 / 500000000000000000)) * (126 / 100) + 8 * ((176180019 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12915) *
          (32 * (((4394340809 / 1000000000000000000) : ℝ) + (1466026511 / 1000000000000000000) + (176180019 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12915 : ℝ) ^ 16 *
      (d.w0 12915 164 + d.w1 12915 164 * √(π / 2) + 2 * d.w2 12915 164 +
        energyR16 12915 * radiusPolynomialRoot16 (d.w0 12915 164) (d.w1 12915 164)
          (d.w2 12915 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12915 : ℝ) ^ 16 *
        (((435789171 / 25000000000000000000) : ℝ) + ((77513919 / 6250000000000000000)) * (126 / 100) + 2 * ((5664323 / 1250000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12915) *
          (32 * (((435789171 / 25000000000000000000) : ℝ) + (77513919 / 6250000000000000000) + (5664323 / 1250000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12915

/-! A coarse bound on the actual paper statistics constant at dimension 12916. -/
namespace BstLean.Part266.Row12916
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12914 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12914 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12914 128 ≤ (13168 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13168 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12916) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12916 : ℕ))
    (by norm_num : (12916 : ℕ) ≤ 16384)
  have ht : paperTail256 12916 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12916 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12916 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12916 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12916 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12916 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12914 128 * √(2 / (12916 : ℝ)) *
      (√(12916 : ℝ) + paperT0 12916 + paperTail256 12916) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12916 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12916 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12916 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12914 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12914 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12916 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12916

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12916
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12916 (61 / 100) 164 (17 / (100 * 12916)) (26 / (10 * 12916)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12916 (61 / 100) 164 (17 / (100 * 12916)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (22651813 / 5000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (175377929 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4467812403 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12916 / 12916 * (61 / 100)) ^ 4 * inverseRadius8 (12916 - 1) /
            envelopeGap 12916 (61 / 100) 164 (17 / (100 * 12916)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12916

namespace BstLean.Part266.Row12916
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12916 164 ≤ (13729663 / 3125000000000000)
  f1 : (tableEnvelope C).f1 12916 164 ≤ (146574319 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (352291889 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12916 164 ≤ (8713761 / 500000000000000000)
  w1 : (tableEnvelope C).w1 12916 164 ≤ (1239934831 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12916 164 ≤ (113260147 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (22651813 / 5000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (22651813 / 5000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (175377929 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4467812403 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1813971 / 500000000) : ℝ) ≤ √(17 / (100 * 12916) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12916) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1064232423 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9364238597 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12916) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12916) ≤ (109493153 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12916) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12916 * (164 : ℝ) ^ 2 + 26 / (10 * 12916) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12916) : ℝ)) (tA 12916 * 164 ^ 2 + 26 / (10 * 12916)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1813971 / 500000000))) * ((22651813 / 5000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1813971 / 500000000)) ^ 3) * ((175377929 / 125000000000000000000000))) + ((4467812403 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1813971 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12916) : ℝ)) d.D d.V d.P (√(tA 12916) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1813971 / 500000000)) ^ 2 * (((1064232423 / 500000000000000)) * ((9364238597 / 250000000000000000)))) + ((4467812403 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12916) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1813971 / 500000000)) * ((22651813 / 5000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12916) : ℝ)) (tA 12916 * 164 ^ 2 + 26 / (10 * 12916)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((22651813 / 5000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1813971 / 500000000)) ^ 2) * ((175377929 / 125000000000000000000000)) + ((4467812403 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12916) : ℝ)) (√(26 / (10 * 12916) : ℝ)) d.D d.V d.P (√(tA 12916) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1813971 / 500000000)) * (((1064232423 / 500000000000000)) * ((9364238597 / 250000000000000000))) + ((4467812403 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12916) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((22651813 / 5000000000000000000) : ℝ) + ((4467812403 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12916

namespace BstLean.Part266.Row12916
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12916 164 ∧
    0 ≤ (tableEnvelope C).f1 12916 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12916 164 ∧
    0 ≤ (tableEnvelope C).w1 12916 164 ∧ 0 ≤ (tableEnvelope C).w2 12916 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12916 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12916 164 ∧ 0 ≤ d.f1 12916 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12916 164 ∧ 0 ≤ d.w1 12916 164 ∧ 0 ≤ d.w2 12916 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12916 ≤ 2 * (228 / 100 : ℝ) / 12916 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12916 ≤ 2 * (370 / 100 : ℝ) / 12916 := by
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
    (completeRAData (tableEnvelope C) 12916 164).locationBound 12916 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12916 164).energyBound 12916 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12916 164) (d.f1 12916 164) d.f2 ≤
      32 * (((13729663 / 3125000000000000) : ℝ) + (146574319 / 100000000000000000) + (352291889 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12916 164) (d.w1 12916 164)
      (d.w2 12916 164) ≤
      32 * (((8713761 / 500000000000000000) : ℝ) + (1239934831 / 100000000000000000000) + (113260147 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12916 164) (d.f1 12916 164) d.f2 ≤
      ((13729663 / 3125000000000000) : ℝ) ^ 2 + 2 * ((13729663 / 3125000000000000)) * ((146574319 / 100000000000000000)) * (126 / 100) +
      2 * (((146574319 / 100000000000000000)) ^ 2 + 2 * ((13729663 / 3125000000000000)) * ((352291889 / 1000000000000000000))) +
      6 * ((146574319 / 100000000000000000)) * ((352291889 / 1000000000000000000)) * (126 / 100) + 8 * ((352291889 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12916 164) (d.f1 12916 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12916 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12916 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12916 164) (d.f1 12916 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12916 164) (d.w1 12916 164) (d.w2 12916 164)
  have hwexpr0 : 0 ≤ d.w0 12916 164 + d.w1 12916 164 * √(π / 2) +
      2 * d.w2 12916 164 + energyR16 12916 *
      radiusPolynomialRoot16 (d.w0 12916 164) (d.w1 12916 164) (d.w2 12916 164) := by
    positivity
  constructor
  · change (12916 : ℝ) ^ 8 * (mA 12916 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12916 164) (d.f1 12916 164) d.f2 + locationR16 12916 *
        radiusPolynomialRoot16 (d.f0 12916 164) (d.f1 12916 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12916 : ℝ) ^ 8 * (mA 12916 : ℝ) ^ 8 *
        ((((13729663 / 3125000000000000) : ℝ) ^ 2 + 2 * ((13729663 / 3125000000000000)) * ((146574319 / 100000000000000000)) * (126 / 100) +
          2 * (((146574319 / 100000000000000000)) ^ 2 + 2 * ((13729663 / 3125000000000000)) * ((352291889 / 1000000000000000000))) +
          6 * ((146574319 / 100000000000000000)) * ((352291889 / 1000000000000000000)) * (126 / 100) + 8 * ((352291889 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12916) *
          (32 * (((13729663 / 3125000000000000) : ℝ) + (146574319 / 100000000000000000) + (352291889 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12916 : ℝ) ^ 16 *
      (d.w0 12916 164 + d.w1 12916 164 * √(π / 2) + 2 * d.w2 12916 164 +
        energyR16 12916 * radiusPolynomialRoot16 (d.w0 12916 164) (d.w1 12916 164)
          (d.w2 12916 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12916 : ℝ) ^ 16 *
        (((8713761 / 500000000000000000) : ℝ) + ((1239934831 / 100000000000000000000)) * (126 / 100) + 2 * ((113260147 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12916) *
          (32 * (((8713761 / 500000000000000000) : ℝ) + (1239934831 / 100000000000000000000) + (113260147 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12916

/-! A coarse bound on the actual paper statistics constant at dimension 12917. -/
namespace BstLean.Part266.Row12917
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12915 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12915 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12915 128 ≤ (13169 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13169 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12917) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12917 : ℕ))
    (by norm_num : (12917 : ℕ) ≤ 16384)
  have ht : paperTail256 12917 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12917 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12917 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12917 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12917 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12917 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12915 128 * √(2 / (12917 : ℝ)) *
      (√(12917 : ℝ) + paperT0 12917 + paperTail256 12917) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12917 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12917 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12917 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12915 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12915 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12917 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12917

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12917
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12917 (61 / 100) 164 (17 / (100 * 12917)) (26 / (10 * 12917)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12917 (61 / 100) 164 (17 / (100 * 12917)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (113232761 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1402588993 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4465019699 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12917 / 12917 * (61 / 100)) ^ 4 * inverseRadius8 (12917 - 1) /
            envelopeGap 12917 (61 / 100) 164 (17 / (100 * 12917)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12917

namespace BstLean.Part266.Row12917
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12917 164 ≤ (878528061 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12917 164 ≤ (91591197 / 62500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (176111831 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12917 164 ≤ (1742347143 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12917 164 ≤ (154955839 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 12917 164 ≤ (45293537 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (113232761 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (113232761 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1402588993 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4465019699 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1813901 / 500000000) : ℝ) ≤ √(17 / (100 * 12917) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12917) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (532054417 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18725577381 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12917) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12917) ≤ (109484677 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12917) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12917 * (164 : ℝ) ^ 2 + 26 / (10 * 12917) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12917) : ℝ)) (tA 12917 * 164 ^ 2 + 26 / (10 * 12917)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1813901 / 500000000))) * ((113232761 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1813901 / 500000000)) ^ 3) * ((1402588993 / 1000000000000000000000000))) + ((4465019699 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1813901 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12917) : ℝ)) d.D d.V d.P (√(tA 12917) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1813901 / 500000000)) ^ 2 * (((532054417 / 250000000000000)) * ((18725577381 / 500000000000000000)))) + ((4465019699 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12917) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1813901 / 500000000)) * ((113232761 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12917) : ℝ)) (tA 12917 * 164 ^ 2 + 26 / (10 * 12917)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((113232761 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1813901 / 500000000)) ^ 2) * ((1402588993 / 1000000000000000000000000)) + ((4465019699 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12917) : ℝ)) (√(26 / (10 * 12917) : ℝ)) d.D d.V d.P (√(tA 12917) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1813901 / 500000000)) * (((532054417 / 250000000000000)) * ((18725577381 / 500000000000000000))) + ((4465019699 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12917) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((113232761 / 25000000000000000000) : ℝ) + ((4465019699 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12917

namespace BstLean.Part266.Row12917
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12917 164 ∧
    0 ≤ (tableEnvelope C).f1 12917 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12917 164 ∧
    0 ≤ (tableEnvelope C).w1 12917 164 ∧ 0 ≤ (tableEnvelope C).w2 12917 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12917 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12917 164 ∧ 0 ≤ d.f1 12917 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12917 164 ∧ 0 ≤ d.w1 12917 164 ∧ 0 ≤ d.w2 12917 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12917 ≤ 2 * (228 / 100 : ℝ) / 12917 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12917 ≤ 2 * (370 / 100 : ℝ) / 12917 := by
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
    (completeRAData (tableEnvelope C) 12917 164).locationBound 12917 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12917 164).energyBound 12917 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12917 164) (d.f1 12917 164) d.f2 ≤
      32 * (((878528061 / 200000000000000000) : ℝ) + (91591197 / 62500000000000000) + (176111831 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12917 164) (d.w1 12917 164)
      (d.w2 12917 164) ≤
      32 * (((1742347143 / 100000000000000000000) : ℝ) + (154955839 / 12500000000000000000) + (45293537 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12917 164) (d.f1 12917 164) d.f2 ≤
      ((878528061 / 200000000000000000) : ℝ) ^ 2 + 2 * ((878528061 / 200000000000000000)) * ((91591197 / 62500000000000000)) * (126 / 100) +
      2 * (((91591197 / 62500000000000000)) ^ 2 + 2 * ((878528061 / 200000000000000000)) * ((176111831 / 500000000000000000))) +
      6 * ((91591197 / 62500000000000000)) * ((176111831 / 500000000000000000)) * (126 / 100) + 8 * ((176111831 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12917 164) (d.f1 12917 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12917 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12917 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12917 164) (d.f1 12917 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12917 164) (d.w1 12917 164) (d.w2 12917 164)
  have hwexpr0 : 0 ≤ d.w0 12917 164 + d.w1 12917 164 * √(π / 2) +
      2 * d.w2 12917 164 + energyR16 12917 *
      radiusPolynomialRoot16 (d.w0 12917 164) (d.w1 12917 164) (d.w2 12917 164) := by
    positivity
  constructor
  · change (12917 : ℝ) ^ 8 * (mA 12917 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12917 164) (d.f1 12917 164) d.f2 + locationR16 12917 *
        radiusPolynomialRoot16 (d.f0 12917 164) (d.f1 12917 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12917 : ℝ) ^ 8 * (mA 12917 : ℝ) ^ 8 *
        ((((878528061 / 200000000000000000) : ℝ) ^ 2 + 2 * ((878528061 / 200000000000000000)) * ((91591197 / 62500000000000000)) * (126 / 100) +
          2 * (((91591197 / 62500000000000000)) ^ 2 + 2 * ((878528061 / 200000000000000000)) * ((176111831 / 500000000000000000))) +
          6 * ((91591197 / 62500000000000000)) * ((176111831 / 500000000000000000)) * (126 / 100) + 8 * ((176111831 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12917) *
          (32 * (((878528061 / 200000000000000000) : ℝ) + (91591197 / 62500000000000000) + (176111831 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12917 : ℝ) ^ 16 *
      (d.w0 12917 164 + d.w1 12917 164 * √(π / 2) + 2 * d.w2 12917 164 +
        energyR16 12917 * radiusPolynomialRoot16 (d.w0 12917 164) (d.w1 12917 164)
          (d.w2 12917 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12917 : ℝ) ^ 16 *
        (((1742347143 / 100000000000000000000) : ℝ) + ((154955839 / 12500000000000000000)) * (126 / 100) + 2 * ((45293537 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12917) *
          (32 * (((1742347143 / 100000000000000000000) : ℝ) + (154955839 / 12500000000000000000) + (45293537 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12917

/-! A coarse bound on the actual paper statistics constant at dimension 12918. -/
namespace BstLean.Part266.Row12918
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12916 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12916 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12916 128 ≤ (13170 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13170 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12918) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12918 : ℕ))
    (by norm_num : (12918 : ℕ) ≤ 16384)
  have ht : paperTail256 12918 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12918 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12918 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12918 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12918 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12918 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12916 128 * √(2 / (12918 : ℝ)) *
      (√(12918 : ℝ) + paperT0 12918 + paperTail256 12918) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12918 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12918 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12918 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12916 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12916 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12918 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12918

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12918
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12918 (61 / 100) 164 (17 / (100 * 12918)) (26 / (10 * 12918)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12918 (61 / 100) 164 (17 / (100 * 12918)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (452825861 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1402154721 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4462228961 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12918 / 12918 * (61 / 100)) ^ 4 * inverseRadius8 (12918 - 1) /
            envelopeGap 12918 (61 / 100) 164 (17 / (100 * 12918)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12918

namespace BstLean.Part266.Row12918
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12918 164 ≤ (878357747 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12918 164 ≤ (366293801 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (5502429 / 15625000000000000)
  w0 : (tableEnvelope C).w0 12918 164 ≤ (1741942223 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12918 164 ≤ (38729959 / 3125000000000000000)
  w2 : (tableEnvelope C).w2 12918 164 ≤ (56603773 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (452825861 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (452825861 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1402154721 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4462228961 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1813831 / 500000000) : ℝ) ≤ √(17 / (100 * 12918) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12918) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1063985269 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9361339117 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12918) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12918) ≤ (109476201 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12918) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12918 * (164 : ℝ) ^ 2 + 26 / (10 * 12918) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12918) : ℝ)) (tA 12918 * 164 ^ 2 + 26 / (10 * 12918)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1813831 / 500000000))) * ((452825861 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1813831 / 500000000)) ^ 3) * ((1402154721 / 1000000000000000000000000))) + ((4462228961 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1813831 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12918) : ℝ)) d.D d.V d.P (√(tA 12918) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1813831 / 500000000)) ^ 2 * (((1063985269 / 500000000000000)) * ((9361339117 / 250000000000000000)))) + ((4462228961 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12918) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1813831 / 500000000)) * ((452825861 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12918) : ℝ)) (tA 12918 * 164 ^ 2 + 26 / (10 * 12918)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((452825861 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1813831 / 500000000)) ^ 2) * ((1402154721 / 1000000000000000000000000)) + ((4462228961 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12918) : ℝ)) (√(26 / (10 * 12918) : ℝ)) d.D d.V d.P (√(tA 12918) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1813831 / 500000000)) * (((1063985269 / 500000000000000)) * ((9361339117 / 250000000000000000))) + ((4462228961 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12918) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((452825861 / 100000000000000000000) : ℝ) + ((4462228961 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12918

namespace BstLean.Part266.Row12918
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12918 164 ∧
    0 ≤ (tableEnvelope C).f1 12918 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12918 164 ∧
    0 ≤ (tableEnvelope C).w1 12918 164 ∧ 0 ≤ (tableEnvelope C).w2 12918 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12918 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12918 164 ∧ 0 ≤ d.f1 12918 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12918 164 ∧ 0 ≤ d.w1 12918 164 ∧ 0 ≤ d.w2 12918 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12918 ≤ 2 * (228 / 100 : ℝ) / 12918 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12918 ≤ 2 * (370 / 100 : ℝ) / 12918 := by
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
    (completeRAData (tableEnvelope C) 12918 164).locationBound 12918 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12918 164).energyBound 12918 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12918 164) (d.f1 12918 164) d.f2 ≤
      32 * (((878357747 / 200000000000000000) : ℝ) + (366293801 / 250000000000000000) + (5502429 / 15625000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12918 164) (d.w1 12918 164)
      (d.w2 12918 164) ≤
      32 * (((1741942223 / 100000000000000000000) : ℝ) + (38729959 / 3125000000000000000) + (56603773 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12918 164) (d.f1 12918 164) d.f2 ≤
      ((878357747 / 200000000000000000) : ℝ) ^ 2 + 2 * ((878357747 / 200000000000000000)) * ((366293801 / 250000000000000000)) * (126 / 100) +
      2 * (((366293801 / 250000000000000000)) ^ 2 + 2 * ((878357747 / 200000000000000000)) * ((5502429 / 15625000000000000))) +
      6 * ((366293801 / 250000000000000000)) * ((5502429 / 15625000000000000)) * (126 / 100) + 8 * ((5502429 / 15625000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12918 164) (d.f1 12918 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12918 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12918 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12918 164) (d.f1 12918 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12918 164) (d.w1 12918 164) (d.w2 12918 164)
  have hwexpr0 : 0 ≤ d.w0 12918 164 + d.w1 12918 164 * √(π / 2) +
      2 * d.w2 12918 164 + energyR16 12918 *
      radiusPolynomialRoot16 (d.w0 12918 164) (d.w1 12918 164) (d.w2 12918 164) := by
    positivity
  constructor
  · change (12918 : ℝ) ^ 8 * (mA 12918 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12918 164) (d.f1 12918 164) d.f2 + locationR16 12918 *
        radiusPolynomialRoot16 (d.f0 12918 164) (d.f1 12918 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12918 : ℝ) ^ 8 * (mA 12918 : ℝ) ^ 8 *
        ((((878357747 / 200000000000000000) : ℝ) ^ 2 + 2 * ((878357747 / 200000000000000000)) * ((366293801 / 250000000000000000)) * (126 / 100) +
          2 * (((366293801 / 250000000000000000)) ^ 2 + 2 * ((878357747 / 200000000000000000)) * ((5502429 / 15625000000000000))) +
          6 * ((366293801 / 250000000000000000)) * ((5502429 / 15625000000000000)) * (126 / 100) + 8 * ((5502429 / 15625000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12918) *
          (32 * (((878357747 / 200000000000000000) : ℝ) + (366293801 / 250000000000000000) + (5502429 / 15625000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12918 : ℝ) ^ 16 *
      (d.w0 12918 164 + d.w1 12918 164 * √(π / 2) + 2 * d.w2 12918 164 +
        energyR16 12918 * radiusPolynomialRoot16 (d.w0 12918 164) (d.w1 12918 164)
          (d.w2 12918 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12918 : ℝ) ^ 16 *
        (((1741942223 / 100000000000000000000) : ℝ) + ((38729959 / 3125000000000000000)) * (126 / 100) + 2 * ((56603773 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12918) *
          (32 * (((1741942223 / 100000000000000000000) : ℝ) + (38729959 / 3125000000000000000) + (56603773 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12918

/-! A coarse bound on the actual paper statistics constant at dimension 12919. -/
namespace BstLean.Part266.Row12919
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12917 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12917 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12917 128 ≤ (13171 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13171 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12919) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12919 : ℕ))
    (by norm_num : (12919 : ℕ) ≤ 16384)
  have ht : paperTail256 12919 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12919 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12919 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12919 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12919 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12919 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12917 128 * √(2 / (12919 : ℝ)) *
      (√(12919 : ℝ) + paperT0 12919 + paperTail256 12919) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12919 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12919 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12919 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12917 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12917 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12919 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12919

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12919
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12919 (61 / 100) 164 (17 / (100 * 12919)) (26 / (10 * 12919)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12919 (61 / 100) 164 (17 / (100 * 12919)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (45272071 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1401720617 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4459440187 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12919 / 12919 * (61 / 100)) ^ 4 * inverseRadius8 (12919 - 1) /
            envelopeGap 12919 (61 / 100) 164 (17 / (100 * 12919)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12919

namespace BstLean.Part266.Row12919
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12919 164 ≤ (2195470473 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12919 164 ≤ (1464892153 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (352087367 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12919 164 ≤ (34830763 / 2000000000000000000)
  w1 : (tableEnvelope C).w1 12919 164 ≤ (1239071099 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12919 164 ≤ (45272503 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (45272071 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (45272071 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1401720617 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4459440187 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3627521 / 1000000000) : ℝ) ≤ √(17 / (100 * 12919) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12919) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (425544691 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (233997247 / 6250000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12919) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12919) ≤ (109467727 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12919) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12919 * (164 : ℝ) ^ 2 + 26 / (10 * 12919) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12919) : ℝ)) (tA 12919 * 164 ^ 2 + 26 / (10 * 12919)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3627521 / 1000000000))) * ((45272071 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3627521 / 1000000000)) ^ 3) * ((1401720617 / 1000000000000000000000000))) + ((4459440187 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3627521 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12919) : ℝ)) d.D d.V d.P (√(tA 12919) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3627521 / 1000000000)) ^ 2 * (((425544691 / 200000000000000)) * ((233997247 / 6250000000000000)))) + ((4459440187 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12919) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3627521 / 1000000000)) * ((45272071 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12919) : ℝ)) (tA 12919 * 164 ^ 2 + 26 / (10 * 12919)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((45272071 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3627521 / 1000000000)) ^ 2) * ((1401720617 / 1000000000000000000000000)) + ((4459440187 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12919) : ℝ)) (√(26 / (10 * 12919) : ℝ)) d.D d.V d.P (√(tA 12919) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3627521 / 1000000000)) * (((425544691 / 200000000000000)) * ((233997247 / 6250000000000000))) + ((4459440187 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12919) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((45272071 / 10000000000000000000) : ℝ) + ((4459440187 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12919

namespace BstLean.Part266.Row12919
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12919 164 ∧
    0 ≤ (tableEnvelope C).f1 12919 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12919 164 ∧
    0 ≤ (tableEnvelope C).w1 12919 164 ∧ 0 ≤ (tableEnvelope C).w2 12919 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12919 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12919 164 ∧ 0 ≤ d.f1 12919 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12919 164 ∧ 0 ≤ d.w1 12919 164 ∧ 0 ≤ d.w2 12919 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12919 ≤ 2 * (228 / 100 : ℝ) / 12919 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12919 ≤ 2 * (370 / 100 : ℝ) / 12919 := by
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
    (completeRAData (tableEnvelope C) 12919 164).locationBound 12919 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12919 164).energyBound 12919 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12919 164) (d.f1 12919 164) d.f2 ≤
      32 * (((2195470473 / 500000000000000000) : ℝ) + (1464892153 / 1000000000000000000) + (352087367 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12919 164) (d.w1 12919 164)
      (d.w2 12919 164) ≤
      32 * (((34830763 / 2000000000000000000) : ℝ) + (1239071099 / 100000000000000000000) + (45272503 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12919 164) (d.f1 12919 164) d.f2 ≤
      ((2195470473 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2195470473 / 500000000000000000)) * ((1464892153 / 1000000000000000000)) * (126 / 100) +
      2 * (((1464892153 / 1000000000000000000)) ^ 2 + 2 * ((2195470473 / 500000000000000000)) * ((352087367 / 1000000000000000000))) +
      6 * ((1464892153 / 1000000000000000000)) * ((352087367 / 1000000000000000000)) * (126 / 100) + 8 * ((352087367 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12919 164) (d.f1 12919 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12919 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12919 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12919 164) (d.f1 12919 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12919 164) (d.w1 12919 164) (d.w2 12919 164)
  have hwexpr0 : 0 ≤ d.w0 12919 164 + d.w1 12919 164 * √(π / 2) +
      2 * d.w2 12919 164 + energyR16 12919 *
      radiusPolynomialRoot16 (d.w0 12919 164) (d.w1 12919 164) (d.w2 12919 164) := by
    positivity
  constructor
  · change (12919 : ℝ) ^ 8 * (mA 12919 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12919 164) (d.f1 12919 164) d.f2 + locationR16 12919 *
        radiusPolynomialRoot16 (d.f0 12919 164) (d.f1 12919 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12919 : ℝ) ^ 8 * (mA 12919 : ℝ) ^ 8 *
        ((((2195470473 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2195470473 / 500000000000000000)) * ((1464892153 / 1000000000000000000)) * (126 / 100) +
          2 * (((1464892153 / 1000000000000000000)) ^ 2 + 2 * ((2195470473 / 500000000000000000)) * ((352087367 / 1000000000000000000))) +
          6 * ((1464892153 / 1000000000000000000)) * ((352087367 / 1000000000000000000)) * (126 / 100) + 8 * ((352087367 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12919) *
          (32 * (((2195470473 / 500000000000000000) : ℝ) + (1464892153 / 1000000000000000000) + (352087367 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12919 : ℝ) ^ 16 *
      (d.w0 12919 164 + d.w1 12919 164 * √(π / 2) + 2 * d.w2 12919 164 +
        energyR16 12919 * radiusPolynomialRoot16 (d.w0 12919 164) (d.w1 12919 164)
          (d.w2 12919 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12919 : ℝ) ^ 16 *
        (((34830763 / 2000000000000000000) : ℝ) + ((1239071099 / 100000000000000000000)) * (126 / 100) + 2 * ((45272503 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12919) *
          (32 * (((34830763 / 2000000000000000000) : ℝ) + (1239071099 / 100000000000000000000) + (45272503 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12919

/-! A coarse bound on the actual paper statistics constant at dimension 12920. -/
namespace BstLean.Part266.Row12920
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12918 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12918 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12918 128 ≤ (13172 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13172 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12920) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12920 : ℕ))
    (by norm_num : (12920 : ℕ) ≤ 16384)
  have ht : paperTail256 12920 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12920 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12920 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12920 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12920 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12920 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12918 128 * √(2 / (12920 : ℝ)) *
      (√(12920 : ℝ) + paperT0 12920 + paperTail256 12920) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12920 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12920 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12920 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12918 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12918 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12920 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12920

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12920
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12920 (61 / 100) 164 (17 / (100 * 12920)) (26 / (10 * 12920)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12920 (61 / 100) 164 (17 / (100 * 12920)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (56576949 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (700643341 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (69635209 / 15625000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12920 / 12920 * (61 / 100)) ^ 4 * inverseRadius8 (12920 - 1) /
            envelopeGap 12920 (61 / 100) 164 (17 / (100 * 12920)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12920

namespace BstLean.Part266.Row12920
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12920 164 ≤ (2195044977 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12920 164 ≤ (732304193 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (352019201 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12920 164 ≤ (27205211 / 1562500000000000000)
  w1 : (tableEnvelope C).w1 12920 164 ≤ (247756653 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12920 164 ≤ (45261991 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (56576949 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (56576949 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (700643341 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (69635209 / 15625000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3627381 / 1000000000) : ℝ) ≤ √(17 / (100 * 12920) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12920) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2127476421 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37433763931 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12920) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12920) ≤ (21891851 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12920) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12920 * (164 : ℝ) ^ 2 + 26 / (10 * 12920) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12920) : ℝ)) (tA 12920 * 164 ^ 2 + 26 / (10 * 12920)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3627381 / 1000000000))) * ((56576949 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3627381 / 1000000000)) ^ 3) * ((700643341 / 500000000000000000000000))) + ((69635209 / 15625000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3627381 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12920) : ℝ)) d.D d.V d.P (√(tA 12920) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3627381 / 1000000000)) ^ 2 * (((2127476421 / 1000000000000000)) * ((37433763931 / 1000000000000000000)))) + ((69635209 / 15625000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12920) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3627381 / 1000000000)) * ((56576949 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12920) : ℝ)) (tA 12920 * 164 ^ 2 + 26 / (10 * 12920)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((56576949 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3627381 / 1000000000)) ^ 2) * ((700643341 / 500000000000000000000000)) + ((69635209 / 15625000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12920) : ℝ)) (√(26 / (10 * 12920) : ℝ)) d.D d.V d.P (√(tA 12920) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3627381 / 1000000000)) * (((2127476421 / 1000000000000000)) * ((37433763931 / 1000000000000000000))) + ((69635209 / 15625000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12920) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((56576949 / 12500000000000000000) : ℝ) + ((69635209 / 15625000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12920

namespace BstLean.Part266.Row12920
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12920 164 ∧
    0 ≤ (tableEnvelope C).f1 12920 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12920 164 ∧
    0 ≤ (tableEnvelope C).w1 12920 164 ∧ 0 ≤ (tableEnvelope C).w2 12920 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12920 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12920 164 ∧ 0 ≤ d.f1 12920 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12920 164 ∧ 0 ≤ d.w1 12920 164 ∧ 0 ≤ d.w2 12920 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12920 ≤ 2 * (228 / 100 : ℝ) / 12920 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12920 ≤ 2 * (370 / 100 : ℝ) / 12920 := by
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
    (completeRAData (tableEnvelope C) 12920 164).locationBound 12920 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12920 164).energyBound 12920 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12920 164) (d.f1 12920 164) d.f2 ≤
      32 * (((2195044977 / 500000000000000000) : ℝ) + (732304193 / 500000000000000000) + (352019201 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12920 164) (d.w1 12920 164)
      (d.w2 12920 164) ≤
      32 * (((27205211 / 1562500000000000000) : ℝ) + (247756653 / 20000000000000000000) + (45261991 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12920 164) (d.f1 12920 164) d.f2 ≤
      ((2195044977 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2195044977 / 500000000000000000)) * ((732304193 / 500000000000000000)) * (126 / 100) +
      2 * (((732304193 / 500000000000000000)) ^ 2 + 2 * ((2195044977 / 500000000000000000)) * ((352019201 / 1000000000000000000))) +
      6 * ((732304193 / 500000000000000000)) * ((352019201 / 1000000000000000000)) * (126 / 100) + 8 * ((352019201 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12920 164) (d.f1 12920 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12920 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12920 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12920 164) (d.f1 12920 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12920 164) (d.w1 12920 164) (d.w2 12920 164)
  have hwexpr0 : 0 ≤ d.w0 12920 164 + d.w1 12920 164 * √(π / 2) +
      2 * d.w2 12920 164 + energyR16 12920 *
      radiusPolynomialRoot16 (d.w0 12920 164) (d.w1 12920 164) (d.w2 12920 164) := by
    positivity
  constructor
  · change (12920 : ℝ) ^ 8 * (mA 12920 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12920 164) (d.f1 12920 164) d.f2 + locationR16 12920 *
        radiusPolynomialRoot16 (d.f0 12920 164) (d.f1 12920 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12920 : ℝ) ^ 8 * (mA 12920 : ℝ) ^ 8 *
        ((((2195044977 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2195044977 / 500000000000000000)) * ((732304193 / 500000000000000000)) * (126 / 100) +
          2 * (((732304193 / 500000000000000000)) ^ 2 + 2 * ((2195044977 / 500000000000000000)) * ((352019201 / 1000000000000000000))) +
          6 * ((732304193 / 500000000000000000)) * ((352019201 / 1000000000000000000)) * (126 / 100) + 8 * ((352019201 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12920) *
          (32 * (((2195044977 / 500000000000000000) : ℝ) + (732304193 / 500000000000000000) + (352019201 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12920 : ℝ) ^ 16 *
      (d.w0 12920 164 + d.w1 12920 164 * √(π / 2) + 2 * d.w2 12920 164 +
        energyR16 12920 * radiusPolynomialRoot16 (d.w0 12920 164) (d.w1 12920 164)
          (d.w2 12920 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12920 : ℝ) ^ 16 *
        (((27205211 / 1562500000000000000) : ℝ) + ((247756653 / 20000000000000000000)) * (126 / 100) + 2 * ((45261991 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12920) *
          (32 * (((27205211 / 1562500000000000000) : ℝ) + (247756653 / 20000000000000000000) + (45261991 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12920

/-! A coarse bound on the actual paper statistics constant at dimension 12921. -/
namespace BstLean.Part266.Row12921
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12919 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12919 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12919 128 ≤ (13173 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13173 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12921) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12921 : ℕ))
    (by norm_num : (12921 : ℕ) ≤ 16384)
  have ht : paperTail256 12921 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12921 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12921 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12921 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12921 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12921 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12919 128 * √(2 / (12921 : ℝ)) *
      (√(12921 : ℝ) + paperT0 12921 + paperTail256 12921) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12921 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12921 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12921 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12919 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12919 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12921 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12921

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12921
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12921 (61 / 100) 164 (17 / (100 * 12921)) (26 / (10 * 12921)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12921 (61 / 100) 164 (17 / (100 * 12921)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (226255253 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (700426457 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2226934263 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12921 / 12921 * (61 / 100)) ^ 4 * inverseRadius8 (12921 - 1) /
            envelopeGap 12921 (61 / 100) 164 (17 / (100 * 12921)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12921

namespace BstLean.Part266.Row12921
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12921 164 ≤ (4389242739 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12921 164 ≤ (292865103 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (351951151 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12921 164 ≤ (217591213 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12921 164 ≤ (619247933 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12921 164 ≤ (452514821 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (226255253 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (226255253 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (700426457 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2226934263 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((90681 / 25000000) : ℝ) ≤ √(17 / (100 * 12921) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12921) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2127229433 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9356992419 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12921) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12921) ≤ (109450783 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12921) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12921 * (164 : ℝ) ^ 2 + 26 / (10 * 12921) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12921) : ℝ)) (tA 12921 * 164 ^ 2 + 26 / (10 * 12921)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((90681 / 25000000))) * ((226255253 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((90681 / 25000000)) ^ 3) * ((700426457 / 500000000000000000000000))) + ((2226934263 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((90681 / 25000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12921) : ℝ)) d.D d.V d.P (√(tA 12921) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((90681 / 25000000)) ^ 2 * (((2127229433 / 1000000000000000)) * ((9356992419 / 250000000000000000)))) + ((2226934263 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12921) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((90681 / 25000000)) * ((226255253 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12921) : ℝ)) (tA 12921 * 164 ^ 2 + 26 / (10 * 12921)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((226255253 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((90681 / 25000000)) ^ 2) * ((700426457 / 500000000000000000000000)) + ((2226934263 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12921) : ℝ)) (√(26 / (10 * 12921) : ℝ)) d.D d.V d.P (√(tA 12921) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((90681 / 25000000)) * (((2127229433 / 1000000000000000)) * ((9356992419 / 250000000000000000))) + ((2226934263 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12921) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((226255253 / 50000000000000000000) : ℝ) + ((2226934263 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12921

namespace BstLean.Part266.Row12921
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12921 164 ∧
    0 ≤ (tableEnvelope C).f1 12921 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12921 164 ∧
    0 ≤ (tableEnvelope C).w1 12921 164 ∧ 0 ≤ (tableEnvelope C).w2 12921 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12921 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12921 164 ∧ 0 ≤ d.f1 12921 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12921 164 ∧ 0 ≤ d.w1 12921 164 ∧ 0 ≤ d.w2 12921 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12921 ≤ 2 * (228 / 100 : ℝ) / 12921 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12921 ≤ 2 * (370 / 100 : ℝ) / 12921 := by
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
    (completeRAData (tableEnvelope C) 12921 164).locationBound 12921 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12921 164).energyBound 12921 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12921 164) (d.f1 12921 164) d.f2 ≤
      32 * (((4389242739 / 1000000000000000000) : ℝ) + (292865103 / 200000000000000000) + (351951151 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12921 164) (d.w1 12921 164)
      (d.w2 12921 164) ≤
      32 * (((217591213 / 12500000000000000000) : ℝ) + (619247933 / 50000000000000000000) + (452514821 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12921 164) (d.f1 12921 164) d.f2 ≤
      ((4389242739 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4389242739 / 1000000000000000000)) * ((292865103 / 200000000000000000)) * (126 / 100) +
      2 * (((292865103 / 200000000000000000)) ^ 2 + 2 * ((4389242739 / 1000000000000000000)) * ((351951151 / 1000000000000000000))) +
      6 * ((292865103 / 200000000000000000)) * ((351951151 / 1000000000000000000)) * (126 / 100) + 8 * ((351951151 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12921 164) (d.f1 12921 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12921 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12921 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12921 164) (d.f1 12921 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12921 164) (d.w1 12921 164) (d.w2 12921 164)
  have hwexpr0 : 0 ≤ d.w0 12921 164 + d.w1 12921 164 * √(π / 2) +
      2 * d.w2 12921 164 + energyR16 12921 *
      radiusPolynomialRoot16 (d.w0 12921 164) (d.w1 12921 164) (d.w2 12921 164) := by
    positivity
  constructor
  · change (12921 : ℝ) ^ 8 * (mA 12921 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12921 164) (d.f1 12921 164) d.f2 + locationR16 12921 *
        radiusPolynomialRoot16 (d.f0 12921 164) (d.f1 12921 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12921 : ℝ) ^ 8 * (mA 12921 : ℝ) ^ 8 *
        ((((4389242739 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4389242739 / 1000000000000000000)) * ((292865103 / 200000000000000000)) * (126 / 100) +
          2 * (((292865103 / 200000000000000000)) ^ 2 + 2 * ((4389242739 / 1000000000000000000)) * ((351951151 / 1000000000000000000))) +
          6 * ((292865103 / 200000000000000000)) * ((351951151 / 1000000000000000000)) * (126 / 100) + 8 * ((351951151 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12921) *
          (32 * (((4389242739 / 1000000000000000000) : ℝ) + (292865103 / 200000000000000000) + (351951151 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12921 : ℝ) ^ 16 *
      (d.w0 12921 164 + d.w1 12921 164 * √(π / 2) + 2 * d.w2 12921 164 +
        energyR16 12921 * radiusPolynomialRoot16 (d.w0 12921 164) (d.w1 12921 164)
          (d.w2 12921 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12921 : ℝ) ^ 16 *
        (((217591213 / 12500000000000000000) : ℝ) + ((619247933 / 50000000000000000000)) * (126 / 100) + 2 * ((452514821 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12921) *
          (32 * (((217591213 / 12500000000000000000) : ℝ) + (619247933 / 50000000000000000000) + (452514821 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12921

/-! A coarse bound on the actual paper statistics constant at dimension 12922. -/
namespace BstLean.Part266.Row12922
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12920 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12920 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12920 128 ≤ (13174 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13174 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12922) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12922 : ℕ))
    (by norm_num : (12922 : ℕ) ≤ 16384)
  have ht : paperTail256 12922 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12922 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12922 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12922 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12922 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12922 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12920 128 * √(2 / (12922 : ℝ)) *
      (√(12922 : ℝ) + paperT0 12922 + paperTail256 12922) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12922 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12922 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12922 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12920 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12920 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12922 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12922

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12922
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12922 (61 / 100) 164 (17 / (100 * 12922)) (26 / (10 * 12922)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12922 (61 / 100) 164 (17 / (100 * 12922)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (452405453 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (700209657 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1112771409 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12922 / 12922 * (61 / 100)) ^ 4 * inverseRadius8 (12922 - 1) /
            envelopeGap 12922 (61 / 100) 164 (17 / (100 * 12922)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12922

namespace BstLean.Part266.Row12922
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12922 164 ≤ (2194196159 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12922 164 ≤ (183005241 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (14075321 / 40000000000000000)
  w0 : (tableEnvelope C).w0 12922 164 ≤ (1740325331 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12922 164 ≤ (1238208221 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12922 164 ≤ (90481953 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (452405453 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (452405453 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (700209657 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1112771409 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((36271 / 10000000) : ℝ) ≤ √(17 / (100 * 12922) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12922) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (425396499 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (73090189 / 1953125000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12922) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12922) ≤ (109442313 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12922) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12922 * (164 : ℝ) ^ 2 + 26 / (10 * 12922) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12922) : ℝ)) (tA 12922 * 164 ^ 2 + 26 / (10 * 12922)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((36271 / 10000000))) * ((452405453 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((36271 / 10000000)) ^ 3) * ((700209657 / 500000000000000000000000))) + ((1112771409 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((36271 / 10000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12922) : ℝ)) d.D d.V d.P (√(tA 12922) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((36271 / 10000000)) ^ 2 * (((425396499 / 200000000000000)) * ((73090189 / 1953125000000000)))) + ((1112771409 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12922) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((36271 / 10000000)) * ((452405453 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12922) : ℝ)) (tA 12922 * 164 ^ 2 + 26 / (10 * 12922)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((452405453 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((36271 / 10000000)) ^ 2) * ((700209657 / 500000000000000000000000)) + ((1112771409 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12922) : ℝ)) (√(26 / (10 * 12922) : ℝ)) d.D d.V d.P (√(tA 12922) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((36271 / 10000000)) * (((425396499 / 200000000000000)) * ((73090189 / 1953125000000000))) + ((1112771409 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12922) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((452405453 / 100000000000000000000) : ℝ) + ((1112771409 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12922

namespace BstLean.Part266.Row12922
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12922 164 ∧
    0 ≤ (tableEnvelope C).f1 12922 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12922 164 ∧
    0 ≤ (tableEnvelope C).w1 12922 164 ∧ 0 ≤ (tableEnvelope C).w2 12922 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12922 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12922 164 ∧ 0 ≤ d.f1 12922 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12922 164 ∧ 0 ≤ d.w1 12922 164 ∧ 0 ≤ d.w2 12922 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12922 ≤ 2 * (228 / 100 : ℝ) / 12922 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12922 ≤ 2 * (370 / 100 : ℝ) / 12922 := by
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
    (completeRAData (tableEnvelope C) 12922 164).locationBound 12922 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12922 164).energyBound 12922 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12922 164) (d.f1 12922 164) d.f2 ≤
      32 * (((2194196159 / 500000000000000000) : ℝ) + (183005241 / 125000000000000000) + (14075321 / 40000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12922 164) (d.w1 12922 164)
      (d.w2 12922 164) ≤
      32 * (((1740325331 / 100000000000000000000) : ℝ) + (1238208221 / 100000000000000000000) + (90481953 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12922 164) (d.f1 12922 164) d.f2 ≤
      ((2194196159 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2194196159 / 500000000000000000)) * ((183005241 / 125000000000000000)) * (126 / 100) +
      2 * (((183005241 / 125000000000000000)) ^ 2 + 2 * ((2194196159 / 500000000000000000)) * ((14075321 / 40000000000000000))) +
      6 * ((183005241 / 125000000000000000)) * ((14075321 / 40000000000000000)) * (126 / 100) + 8 * ((14075321 / 40000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12922 164) (d.f1 12922 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12922 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12922 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12922 164) (d.f1 12922 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12922 164) (d.w1 12922 164) (d.w2 12922 164)
  have hwexpr0 : 0 ≤ d.w0 12922 164 + d.w1 12922 164 * √(π / 2) +
      2 * d.w2 12922 164 + energyR16 12922 *
      radiusPolynomialRoot16 (d.w0 12922 164) (d.w1 12922 164) (d.w2 12922 164) := by
    positivity
  constructor
  · change (12922 : ℝ) ^ 8 * (mA 12922 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12922 164) (d.f1 12922 164) d.f2 + locationR16 12922 *
        radiusPolynomialRoot16 (d.f0 12922 164) (d.f1 12922 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12922 : ℝ) ^ 8 * (mA 12922 : ℝ) ^ 8 *
        ((((2194196159 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2194196159 / 500000000000000000)) * ((183005241 / 125000000000000000)) * (126 / 100) +
          2 * (((183005241 / 125000000000000000)) ^ 2 + 2 * ((2194196159 / 500000000000000000)) * ((14075321 / 40000000000000000))) +
          6 * ((183005241 / 125000000000000000)) * ((14075321 / 40000000000000000)) * (126 / 100) + 8 * ((14075321 / 40000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12922) *
          (32 * (((2194196159 / 500000000000000000) : ℝ) + (183005241 / 125000000000000000) + (14075321 / 40000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12922 : ℝ) ^ 16 *
      (d.w0 12922 164 + d.w1 12922 164 * √(π / 2) + 2 * d.w2 12922 164 +
        energyR16 12922 * radiusPolynomialRoot16 (d.w0 12922 164) (d.w1 12922 164)
          (d.w2 12922 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12922 : ℝ) ^ 16 *
        (((1740325331 / 100000000000000000000) : ℝ) + ((1238208221 / 100000000000000000000)) * (126 / 100) + 2 * ((90481953 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12922) *
          (32 * (((1740325331 / 100000000000000000000) : ℝ) + (1238208221 / 100000000000000000000) + (90481953 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12922

/-! A coarse bound on the actual paper statistics constant at dimension 12923. -/
namespace BstLean.Part266.Row12923
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12921 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12921 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12921 128 ≤ (13175 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13175 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12923) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12923 : ℕ))
    (by norm_num : (12923 : ℕ) ≤ 16384)
  have ht : paperTail256 12923 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12923 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12923 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12923 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12923 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12923 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12921 128 * √(2 / (12923 : ℝ)) *
      (√(12923 : ℝ) + paperT0 12923 + paperTail256 12923) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12923 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12923 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12923 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12921 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12921 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12923 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12923

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12923
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12923 (61 / 100) 164 (17 / (100 * 12923)) (26 / (10 * 12923)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12923 (61 / 100) 164 (17 / (100 * 12923)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (28268777 / 6250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (699992941 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4448304703 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12923 / 12923 * (61 / 100)) ^ 4 * inverseRadius8 (12923 - 1) /
            envelopeGap 12923 (61 / 100) 164 (17 / (100 * 12923)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12923

namespace BstLean.Part266.Row12923
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12923 164 ≤ (2193771093 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12923 164 ≤ (1463758429 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (351814919 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12923 164 ≤ (869960547 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12923 164 ≤ (1237920669 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12923 164 ≤ (226152371 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (28268777 / 6250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (28268777 / 6250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (699992941 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4448304703 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((45337 / 12500000) : ℝ) ≤ √(17 / (100 * 12923) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12923) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1063367801 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4677048151 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12923) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12923) ≤ (27358461 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12923) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12923 * (164 : ℝ) ^ 2 + 26 / (10 * 12923) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12923) : ℝ)) (tA 12923 * 164 ^ 2 + 26 / (10 * 12923)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((45337 / 12500000))) * ((28268777 / 6250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((45337 / 12500000)) ^ 3) * ((699992941 / 500000000000000000000000))) + ((4448304703 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((45337 / 12500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12923) : ℝ)) d.D d.V d.P (√(tA 12923) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((45337 / 12500000)) ^ 2 * (((1063367801 / 500000000000000)) * ((4677048151 / 125000000000000000)))) + ((4448304703 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12923) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((45337 / 12500000)) * ((28268777 / 6250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12923) : ℝ)) (tA 12923 * 164 ^ 2 + 26 / (10 * 12923)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((28268777 / 6250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((45337 / 12500000)) ^ 2) * ((699992941 / 500000000000000000000000)) + ((4448304703 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12923) : ℝ)) (√(26 / (10 * 12923) : ℝ)) d.D d.V d.P (√(tA 12923) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((45337 / 12500000)) * (((1063367801 / 500000000000000)) * ((4677048151 / 125000000000000000))) + ((4448304703 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12923) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((28268777 / 6250000000000000000) : ℝ) + ((4448304703 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12923

namespace BstLean.Part266.Row12923
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12923 164 ∧
    0 ≤ (tableEnvelope C).f1 12923 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12923 164 ∧
    0 ≤ (tableEnvelope C).w1 12923 164 ∧ 0 ≤ (tableEnvelope C).w2 12923 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12923 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12923 164 ∧ 0 ≤ d.f1 12923 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12923 164 ∧ 0 ≤ d.w1 12923 164 ∧ 0 ≤ d.w2 12923 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12923 ≤ 2 * (228 / 100 : ℝ) / 12923 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12923 ≤ 2 * (370 / 100 : ℝ) / 12923 := by
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
    (completeRAData (tableEnvelope C) 12923 164).locationBound 12923 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12923 164).energyBound 12923 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12923 164) (d.f1 12923 164) d.f2 ≤
      32 * (((2193771093 / 500000000000000000) : ℝ) + (1463758429 / 1000000000000000000) + (351814919 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12923 164) (d.w1 12923 164)
      (d.w2 12923 164) ≤
      32 * (((869960547 / 50000000000000000000) : ℝ) + (1237920669 / 100000000000000000000) + (226152371 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12923 164) (d.f1 12923 164) d.f2 ≤
      ((2193771093 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2193771093 / 500000000000000000)) * ((1463758429 / 1000000000000000000)) * (126 / 100) +
      2 * (((1463758429 / 1000000000000000000)) ^ 2 + 2 * ((2193771093 / 500000000000000000)) * ((351814919 / 1000000000000000000))) +
      6 * ((1463758429 / 1000000000000000000)) * ((351814919 / 1000000000000000000)) * (126 / 100) + 8 * ((351814919 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12923 164) (d.f1 12923 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12923 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12923 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12923 164) (d.f1 12923 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12923 164) (d.w1 12923 164) (d.w2 12923 164)
  have hwexpr0 : 0 ≤ d.w0 12923 164 + d.w1 12923 164 * √(π / 2) +
      2 * d.w2 12923 164 + energyR16 12923 *
      radiusPolynomialRoot16 (d.w0 12923 164) (d.w1 12923 164) (d.w2 12923 164) := by
    positivity
  constructor
  · change (12923 : ℝ) ^ 8 * (mA 12923 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12923 164) (d.f1 12923 164) d.f2 + locationR16 12923 *
        radiusPolynomialRoot16 (d.f0 12923 164) (d.f1 12923 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12923 : ℝ) ^ 8 * (mA 12923 : ℝ) ^ 8 *
        ((((2193771093 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2193771093 / 500000000000000000)) * ((1463758429 / 1000000000000000000)) * (126 / 100) +
          2 * (((1463758429 / 1000000000000000000)) ^ 2 + 2 * ((2193771093 / 500000000000000000)) * ((351814919 / 1000000000000000000))) +
          6 * ((1463758429 / 1000000000000000000)) * ((351814919 / 1000000000000000000)) * (126 / 100) + 8 * ((351814919 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12923) *
          (32 * (((2193771093 / 500000000000000000) : ℝ) + (1463758429 / 1000000000000000000) + (351814919 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12923 : ℝ) ^ 16 *
      (d.w0 12923 164 + d.w1 12923 164 * √(π / 2) + 2 * d.w2 12923 164 +
        energyR16 12923 * radiusPolynomialRoot16 (d.w0 12923 164) (d.w1 12923 164)
          (d.w2 12923 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12923 : ℝ) ^ 16 *
        (((869960547 / 50000000000000000000) : ℝ) + ((1237920669 / 100000000000000000000)) * (126 / 100) + 2 * ((226152371 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12923) *
          (32 * (((869960547 / 50000000000000000000) : ℝ) + (1237920669 / 100000000000000000000) + (226152371 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12923

/-! A coarse bound on the actual paper statistics constant at dimension 12924. -/
namespace BstLean.Part266.Row12924
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12922 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12922 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12922 128 ≤ (13176 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13176 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12924) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12924 : ℕ))
    (by norm_num : (12924 : ℕ) ≤ 16384)
  have ht : paperTail256 12924 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12924 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12924 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12924 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12924 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12924 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12922 128 * √(2 / (12924 : ℝ)) *
      (√(12924 : ℝ) + paperT0 12924 + paperTail256 12924) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12924 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12924 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12924 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12922 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12922 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12924 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12924

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12924
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12924 (61 / 100) 164 (17 / (100 * 12924)) (26 / (10 * 12924)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12924 (61 / 100) 164 (17 / (100 * 12924)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (113048861 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1399552617 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4445525727 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12924 / 12924 * (61 / 100)) ^ 4 * inverseRadius8 (12924 - 1) /
            envelopeGap 12924 (61 / 100) 164 (17 / (100 * 12924)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12924

namespace BstLean.Part266.Row12924
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12924 164 ≤ (438669583 / 100000000000000000)
  f1 : (tableEnvelope C).f1 12924 164 ≤ (365868957 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (35174693 / 100000000000000000)
  w0 : (tableEnvelope C).w0 12924 164 ≤ (217439713 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12924 164 ≤ (618816777 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12924 164 ≤ (452199751 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (113048861 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (113048861 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1399552617 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4445525727 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3626819 / 1000000000) : ℝ) ≤ √(17 / (100 * 12924) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12924) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2126488759 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4676324373 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12924) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12924) ≤ (109425377 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12924) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12924 * (164 : ℝ) ^ 2 + 26 / (10 * 12924) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12924) : ℝ)) (tA 12924 * 164 ^ 2 + 26 / (10 * 12924)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3626819 / 1000000000))) * ((113048861 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3626819 / 1000000000)) ^ 3) * ((1399552617 / 1000000000000000000000000))) + ((4445525727 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3626819 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12924) : ℝ)) d.D d.V d.P (√(tA 12924) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3626819 / 1000000000)) ^ 2 * (((2126488759 / 1000000000000000)) * ((4676324373 / 125000000000000000)))) + ((4445525727 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12924) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3626819 / 1000000000)) * ((113048861 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12924) : ℝ)) (tA 12924 * 164 ^ 2 + 26 / (10 * 12924)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((113048861 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3626819 / 1000000000)) ^ 2) * ((1399552617 / 1000000000000000000000000)) + ((4445525727 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12924) : ℝ)) (√(26 / (10 * 12924) : ℝ)) d.D d.V d.P (√(tA 12924) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3626819 / 1000000000)) * (((2126488759 / 1000000000000000)) * ((4676324373 / 125000000000000000))) + ((4445525727 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12924) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((113048861 / 25000000000000000000) : ℝ) + ((4445525727 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12924

namespace BstLean.Part266.Row12924
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12924 164 ∧
    0 ≤ (tableEnvelope C).f1 12924 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12924 164 ∧
    0 ≤ (tableEnvelope C).w1 12924 164 ∧ 0 ≤ (tableEnvelope C).w2 12924 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12924 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12924 164 ∧ 0 ≤ d.f1 12924 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12924 164 ∧ 0 ≤ d.w1 12924 164 ∧ 0 ≤ d.w2 12924 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12924 ≤ 2 * (228 / 100 : ℝ) / 12924 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12924 ≤ 2 * (370 / 100 : ℝ) / 12924 := by
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
    (completeRAData (tableEnvelope C) 12924 164).locationBound 12924 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12924 164).energyBound 12924 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12924 164) (d.f1 12924 164) d.f2 ≤
      32 * (((438669583 / 100000000000000000) : ℝ) + (365868957 / 250000000000000000) + (35174693 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12924 164) (d.w1 12924 164)
      (d.w2 12924 164) ≤
      32 * (((217439713 / 12500000000000000000) : ℝ) + (618816777 / 50000000000000000000) + (452199751 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12924 164) (d.f1 12924 164) d.f2 ≤
      ((438669583 / 100000000000000000) : ℝ) ^ 2 + 2 * ((438669583 / 100000000000000000)) * ((365868957 / 250000000000000000)) * (126 / 100) +
      2 * (((365868957 / 250000000000000000)) ^ 2 + 2 * ((438669583 / 100000000000000000)) * ((35174693 / 100000000000000000))) +
      6 * ((365868957 / 250000000000000000)) * ((35174693 / 100000000000000000)) * (126 / 100) + 8 * ((35174693 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12924 164) (d.f1 12924 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12924 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12924 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12924 164) (d.f1 12924 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12924 164) (d.w1 12924 164) (d.w2 12924 164)
  have hwexpr0 : 0 ≤ d.w0 12924 164 + d.w1 12924 164 * √(π / 2) +
      2 * d.w2 12924 164 + energyR16 12924 *
      radiusPolynomialRoot16 (d.w0 12924 164) (d.w1 12924 164) (d.w2 12924 164) := by
    positivity
  constructor
  · change (12924 : ℝ) ^ 8 * (mA 12924 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12924 164) (d.f1 12924 164) d.f2 + locationR16 12924 *
        radiusPolynomialRoot16 (d.f0 12924 164) (d.f1 12924 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12924 : ℝ) ^ 8 * (mA 12924 : ℝ) ^ 8 *
        ((((438669583 / 100000000000000000) : ℝ) ^ 2 + 2 * ((438669583 / 100000000000000000)) * ((365868957 / 250000000000000000)) * (126 / 100) +
          2 * (((365868957 / 250000000000000000)) ^ 2 + 2 * ((438669583 / 100000000000000000)) * ((35174693 / 100000000000000000))) +
          6 * ((365868957 / 250000000000000000)) * ((35174693 / 100000000000000000)) * (126 / 100) + 8 * ((35174693 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12924) *
          (32 * (((438669583 / 100000000000000000) : ℝ) + (365868957 / 250000000000000000) + (35174693 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12924 : ℝ) ^ 16 *
      (d.w0 12924 164 + d.w1 12924 164 * √(π / 2) + 2 * d.w2 12924 164 +
        energyR16 12924 * radiusPolynomialRoot16 (d.w0 12924 164) (d.w1 12924 164)
          (d.w2 12924 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12924 : ℝ) ^ 16 *
        (((217439713 / 12500000000000000000) : ℝ) + ((618816777 / 50000000000000000000)) * (126 / 100) + 2 * ((452199751 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12924) *
          (32 * (((217439713 / 12500000000000000000) : ℝ) + (618816777 / 50000000000000000000) + (452199751 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12924
