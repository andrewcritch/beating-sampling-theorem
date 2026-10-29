import BstLean.Part266Shard33Step4


/-! A coarse bound on the actual paper statistics constant at dimension 13175. -/
namespace BstLean.Part266.Row13175
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13173 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13173 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13173 128 ≤ (13427 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13427 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13175) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13175 : ℕ))
    (by norm_num : (13175 : ℕ) ≤ 16384)
  have ht : paperTail256 13175 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13175 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13175 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13175 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13175 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13175 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13173 128 * √(2 / (13175 : ℝ)) *
      (√(13175 : ℝ) + paperT0 13175 + paperTail256 13175) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13175 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13175 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13175 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13173 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13173 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13175 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13175

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13175
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13175 (61 / 100) 166 (17 / (100 * 13175)) (26 / (10 * 13175)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13175 (61 / 100) 166 (17 / (100 * 13175)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (426838789 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1295905257 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (761869093 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13175 / 13175 * (61 / 100)) ^ 4 * inverseRadius8 (13175 - 1) /
            envelopeGap 13175 (61 / 100) 166 (17 / (100 * 13175)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13175

namespace BstLean.Part266.Row13175
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13175 166 ≤ (4180726579 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13175 166 ≤ (174345157 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (167615723 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13175 166 ≤ (205246799 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 13175 166 ≤ (233646697 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 13175 166 ≤ (5335531 / 1250000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (426838789 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (426838789 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1295905257 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (761869093 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1796053 / 500000000) : ℝ) ≤ √(17 / (100 * 13175) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13175) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1033003859 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (35998684101 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13175) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13175) ≤ (6708793 / 62500000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13175) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13175 * (166 : ℝ) ^ 2 + 26 / (10 * 13175) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13175) : ℝ)) (tA 13175 * 166 ^ 2 + 26 / (10 * 13175)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1796053 / 500000000))) * ((426838789 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1796053 / 500000000)) ^ 3) * ((1295905257 / 1000000000000000000000000))) + ((761869093 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1796053 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13175) : ℝ)) d.D d.V d.P (√(tA 13175) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1796053 / 500000000)) ^ 2 * (((1033003859 / 500000000000000)) * ((35998684101 / 1000000000000000000)))) + ((761869093 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13175) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1796053 / 500000000)) * ((426838789 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13175) : ℝ)) (tA 13175 * 166 ^ 2 + 26 / (10 * 13175)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((426838789 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1796053 / 500000000)) ^ 2) * ((1295905257 / 1000000000000000000000000)) + ((761869093 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13175) : ℝ)) (√(26 / (10 * 13175) : ℝ)) d.D d.V d.P (√(tA 13175) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1796053 / 500000000)) * (((1033003859 / 500000000000000)) * ((35998684101 / 1000000000000000000))) + ((761869093 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13175) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((426838789 / 100000000000000000000) : ℝ) + ((761869093 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13175

namespace BstLean.Part266.Row13175
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13175 166 ∧
    0 ≤ (tableEnvelope C).f1 13175 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13175 166 ∧
    0 ≤ (tableEnvelope C).w1 13175 166 ∧ 0 ≤ (tableEnvelope C).w2 13175 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13175 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13175 166 ∧ 0 ≤ d.f1 13175 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13175 166 ∧ 0 ≤ d.w1 13175 166 ∧ 0 ≤ d.w2 13175 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13175 ≤ 2 * (228 / 100 : ℝ) / 13175 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13175 ≤ 2 * (370 / 100 : ℝ) / 13175 := by
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
    (completeRAData (tableEnvelope C) 13175 166).locationBound 13175 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13175 166).energyBound 13175 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13175 166) (d.f1 13175 166) d.f2 ≤
      32 * (((4180726579 / 1000000000000000000) : ℝ) + (174345157 / 125000000000000000) + (167615723 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13175 166) (d.w1 13175 166)
      (d.w2 13175 166) ≤
      32 * (((205246799 / 12500000000000000000) : ℝ) + (233646697 / 20000000000000000000) + (5335531 / 1250000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13175 166) (d.f1 13175 166) d.f2 ≤
      ((4180726579 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4180726579 / 1000000000000000000)) * ((174345157 / 125000000000000000)) * (126 / 100) +
      2 * (((174345157 / 125000000000000000)) ^ 2 + 2 * ((4180726579 / 1000000000000000000)) * ((167615723 / 500000000000000000))) +
      6 * ((174345157 / 125000000000000000)) * ((167615723 / 500000000000000000)) * (126 / 100) + 8 * ((167615723 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13175 166) (d.f1 13175 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13175 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13175 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13175 166) (d.f1 13175 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13175 166) (d.w1 13175 166) (d.w2 13175 166)
  have hwexpr0 : 0 ≤ d.w0 13175 166 + d.w1 13175 166 * √(π / 2) +
      2 * d.w2 13175 166 + energyR16 13175 *
      radiusPolynomialRoot16 (d.w0 13175 166) (d.w1 13175 166) (d.w2 13175 166) := by
    positivity
  constructor
  · change (13175 : ℝ) ^ 8 * (mA 13175 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13175 166) (d.f1 13175 166) d.f2 + locationR16 13175 *
        radiusPolynomialRoot16 (d.f0 13175 166) (d.f1 13175 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13175 : ℝ) ^ 8 * (mA 13175 : ℝ) ^ 8 *
        ((((4180726579 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4180726579 / 1000000000000000000)) * ((174345157 / 125000000000000000)) * (126 / 100) +
          2 * (((174345157 / 125000000000000000)) ^ 2 + 2 * ((4180726579 / 1000000000000000000)) * ((167615723 / 500000000000000000))) +
          6 * ((174345157 / 125000000000000000)) * ((167615723 / 500000000000000000)) * (126 / 100) + 8 * ((167615723 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13175) *
          (32 * (((4180726579 / 1000000000000000000) : ℝ) + (174345157 / 125000000000000000) + (167615723 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13175 : ℝ) ^ 16 *
      (d.w0 13175 166 + d.w1 13175 166 * √(π / 2) + 2 * d.w2 13175 166 +
        energyR16 13175 * radiusPolynomialRoot16 (d.w0 13175 166) (d.w1 13175 166)
          (d.w2 13175 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13175 : ℝ) ^ 16 *
        (((205246799 / 12500000000000000000) : ℝ) + ((233646697 / 20000000000000000000)) * (126 / 100) + 2 * ((5335531 / 1250000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13175) *
          (32 * (((205246799 / 12500000000000000000) : ℝ) + (233646697 / 20000000000000000000) + (5335531 / 1250000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13175

/-! A coarse bound on the actual paper statistics constant at dimension 13176. -/
namespace BstLean.Part266.Row13176
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13174 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13174 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13174 128 ≤ (13428 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13428 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13176) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13176 : ℕ))
    (by norm_num : (13176 : ℕ) ≤ 16384)
  have ht : paperTail256 13176 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13176 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13176 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13176 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13176 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13176 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13174 128 * √(2 / (13176 : ℝ)) *
      (√(13176 : ℝ) + paperT0 13176 + paperTail256 13176) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13176 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13176 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13176 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13174 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13174 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13176 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13176

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13176
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13176 (61 / 100) 166 (17 / (100 * 13176)) (26 / (10 * 13176)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13176 (61 / 100) 166 (17 / (100 * 13176)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (85348321 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1295511873 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (761402297 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13176 / 13176 * (61 / 100)) ^ 4 * inverseRadius8 (13176 - 1) /
            envelopeGap 13176 (61 / 100) 166 (17 / (100 * 13176)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13176

namespace BstLean.Part266.Row13176
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13176 166 ≤ (4179935629 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13176 166 ≤ (278899429 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (335167903 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13176 166 ≤ (102600063 / 6250000000000000000)
  w1 : (tableEnvelope C).w1 13176 166 ≤ (1167967721 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13176 166 ≤ (426745293 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (85348321 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (85348321 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1295511873 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (761402297 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3591969 / 1000000000) : ℝ) ≤ √(17 / (100 * 13176) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13176) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2065772507 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1799660991 / 50000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13176) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13176) ≤ (53666271 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13176) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13176 * (166 : ℝ) ^ 2 + 26 / (10 * 13176) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13176) : ℝ)) (tA 13176 * 166 ^ 2 + 26 / (10 * 13176)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3591969 / 1000000000))) * ((85348321 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3591969 / 1000000000)) ^ 3) * ((1295511873 / 1000000000000000000000000))) + ((761402297 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3591969 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13176) : ℝ)) d.D d.V d.P (√(tA 13176) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3591969 / 1000000000)) ^ 2 * (((2065772507 / 1000000000000000)) * ((1799660991 / 50000000000000000)))) + ((761402297 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13176) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3591969 / 1000000000)) * ((85348321 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13176) : ℝ)) (tA 13176 * 166 ^ 2 + 26 / (10 * 13176)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((85348321 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3591969 / 1000000000)) ^ 2) * ((1295511873 / 1000000000000000000000000)) + ((761402297 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13176) : ℝ)) (√(26 / (10 * 13176) : ℝ)) d.D d.V d.P (√(tA 13176) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3591969 / 1000000000)) * (((2065772507 / 1000000000000000)) * ((1799660991 / 50000000000000000))) + ((761402297 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13176) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((85348321 / 20000000000000000000) : ℝ) + ((761402297 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13176

namespace BstLean.Part266.Row13176
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13176 166 ∧
    0 ≤ (tableEnvelope C).f1 13176 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13176 166 ∧
    0 ≤ (tableEnvelope C).w1 13176 166 ∧ 0 ≤ (tableEnvelope C).w2 13176 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13176 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13176 166 ∧ 0 ≤ d.f1 13176 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13176 166 ∧ 0 ≤ d.w1 13176 166 ∧ 0 ≤ d.w2 13176 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13176 ≤ 2 * (228 / 100 : ℝ) / 13176 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13176 ≤ 2 * (370 / 100 : ℝ) / 13176 := by
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
    (completeRAData (tableEnvelope C) 13176 166).locationBound 13176 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13176 166).energyBound 13176 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13176 166) (d.f1 13176 166) d.f2 ≤
      32 * (((4179935629 / 1000000000000000000) : ℝ) + (278899429 / 200000000000000000) + (335167903 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13176 166) (d.w1 13176 166)
      (d.w2 13176 166) ≤
      32 * (((102600063 / 6250000000000000000) : ℝ) + (1167967721 / 100000000000000000000) + (426745293 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13176 166) (d.f1 13176 166) d.f2 ≤
      ((4179935629 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4179935629 / 1000000000000000000)) * ((278899429 / 200000000000000000)) * (126 / 100) +
      2 * (((278899429 / 200000000000000000)) ^ 2 + 2 * ((4179935629 / 1000000000000000000)) * ((335167903 / 1000000000000000000))) +
      6 * ((278899429 / 200000000000000000)) * ((335167903 / 1000000000000000000)) * (126 / 100) + 8 * ((335167903 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13176 166) (d.f1 13176 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13176 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13176 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13176 166) (d.f1 13176 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13176 166) (d.w1 13176 166) (d.w2 13176 166)
  have hwexpr0 : 0 ≤ d.w0 13176 166 + d.w1 13176 166 * √(π / 2) +
      2 * d.w2 13176 166 + energyR16 13176 *
      radiusPolynomialRoot16 (d.w0 13176 166) (d.w1 13176 166) (d.w2 13176 166) := by
    positivity
  constructor
  · change (13176 : ℝ) ^ 8 * (mA 13176 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13176 166) (d.f1 13176 166) d.f2 + locationR16 13176 *
        radiusPolynomialRoot16 (d.f0 13176 166) (d.f1 13176 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13176 : ℝ) ^ 8 * (mA 13176 : ℝ) ^ 8 *
        ((((4179935629 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4179935629 / 1000000000000000000)) * ((278899429 / 200000000000000000)) * (126 / 100) +
          2 * (((278899429 / 200000000000000000)) ^ 2 + 2 * ((4179935629 / 1000000000000000000)) * ((335167903 / 1000000000000000000))) +
          6 * ((278899429 / 200000000000000000)) * ((335167903 / 1000000000000000000)) * (126 / 100) + 8 * ((335167903 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13176) *
          (32 * (((4179935629 / 1000000000000000000) : ℝ) + (278899429 / 200000000000000000) + (335167903 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13176 : ℝ) ^ 16 *
      (d.w0 13176 166 + d.w1 13176 166 * √(π / 2) + 2 * d.w2 13176 166 +
        energyR16 13176 * radiusPolynomialRoot16 (d.w0 13176 166) (d.w1 13176 166)
          (d.w2 13176 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13176 : ℝ) ^ 16 *
        (((102600063 / 6250000000000000000) : ℝ) + ((1167967721 / 100000000000000000000)) * (126 / 100) + 2 * ((426745293 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13176) *
          (32 * (((102600063 / 6250000000000000000) : ℝ) + (1167967721 / 100000000000000000000) + (426745293 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13176

/-! A coarse bound on the actual paper statistics constant at dimension 13177. -/
namespace BstLean.Part266.Row13177
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13175 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13175 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13175 128 ≤ (13429 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13429 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13177) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13177 : ℕ))
    (by norm_num : (13177 : ℕ) ≤ 16384)
  have ht : paperTail256 13177 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13177 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13177 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13177 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13177 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13177 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13175 128 * √(2 / (13177 : ℝ)) *
      (√(13177 : ℝ) + paperT0 13177 + paperTail256 13177) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13177 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13177 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13177 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13175 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13175 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13177 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13177

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13177
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13177 (61 / 100) 166 (17 / (100 * 13177)) (26 / (10 * 13177)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13177 (61 / 100) 166 (17 / (100 * 13177)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (106661113 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1295118639 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (951169779 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13177 / 13177 * (61 / 100)) ^ 4 * inverseRadius8 (13177 - 1) /
            envelopeGap 13177 (61 / 100) 166 (17 / (100 * 13177)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13177

namespace BstLean.Part266.Row13177
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13177 166 ≤ (2089570793 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13177 166 ≤ (1394232343 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (167552143 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13177 166 ≤ (820613537 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13177 166 ≤ (1167701721 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13177 166 ≤ (213324069 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (106661113 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (106661113 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1295118639 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (951169779 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3591833 / 1000000000) : ℝ) ≤ √(17 / (100 * 13177) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13177) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (413107469 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (17993878397 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13177) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13177) ≤ (26831099 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13177) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13177 * (166 : ℝ) ^ 2 + 26 / (10 * 13177) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13177) : ℝ)) (tA 13177 * 166 ^ 2 + 26 / (10 * 13177)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3591833 / 1000000000))) * ((106661113 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3591833 / 1000000000)) ^ 3) * ((1295118639 / 1000000000000000000000000))) + ((951169779 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3591833 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13177) : ℝ)) d.D d.V d.P (√(tA 13177) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3591833 / 1000000000)) ^ 2 * (((413107469 / 200000000000000)) * ((17993878397 / 500000000000000000)))) + ((951169779 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13177) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3591833 / 1000000000)) * ((106661113 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13177) : ℝ)) (tA 13177 * 166 ^ 2 + 26 / (10 * 13177)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((106661113 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3591833 / 1000000000)) ^ 2) * ((1295118639 / 1000000000000000000000000)) + ((951169779 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13177) : ℝ)) (√(26 / (10 * 13177) : ℝ)) d.D d.V d.P (√(tA 13177) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3591833 / 1000000000)) * (((413107469 / 200000000000000)) * ((17993878397 / 500000000000000000))) + ((951169779 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13177) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((106661113 / 25000000000000000000) : ℝ) + ((951169779 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13177

namespace BstLean.Part266.Row13177
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13177 166 ∧
    0 ≤ (tableEnvelope C).f1 13177 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13177 166 ∧
    0 ≤ (tableEnvelope C).w1 13177 166 ∧ 0 ≤ (tableEnvelope C).w2 13177 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13177 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13177 166 ∧ 0 ≤ d.f1 13177 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13177 166 ∧ 0 ≤ d.w1 13177 166 ∧ 0 ≤ d.w2 13177 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13177 ≤ 2 * (228 / 100 : ℝ) / 13177 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13177 ≤ 2 * (370 / 100 : ℝ) / 13177 := by
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
    (completeRAData (tableEnvelope C) 13177 166).locationBound 13177 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13177 166).energyBound 13177 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13177 166) (d.f1 13177 166) d.f2 ≤
      32 * (((2089570793 / 500000000000000000) : ℝ) + (1394232343 / 1000000000000000000) + (167552143 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13177 166) (d.w1 13177 166)
      (d.w2 13177 166) ≤
      32 * (((820613537 / 50000000000000000000) : ℝ) + (1167701721 / 100000000000000000000) + (213324069 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13177 166) (d.f1 13177 166) d.f2 ≤
      ((2089570793 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2089570793 / 500000000000000000)) * ((1394232343 / 1000000000000000000)) * (126 / 100) +
      2 * (((1394232343 / 1000000000000000000)) ^ 2 + 2 * ((2089570793 / 500000000000000000)) * ((167552143 / 500000000000000000))) +
      6 * ((1394232343 / 1000000000000000000)) * ((167552143 / 500000000000000000)) * (126 / 100) + 8 * ((167552143 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13177 166) (d.f1 13177 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13177 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13177 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13177 166) (d.f1 13177 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13177 166) (d.w1 13177 166) (d.w2 13177 166)
  have hwexpr0 : 0 ≤ d.w0 13177 166 + d.w1 13177 166 * √(π / 2) +
      2 * d.w2 13177 166 + energyR16 13177 *
      radiusPolynomialRoot16 (d.w0 13177 166) (d.w1 13177 166) (d.w2 13177 166) := by
    positivity
  constructor
  · change (13177 : ℝ) ^ 8 * (mA 13177 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13177 166) (d.f1 13177 166) d.f2 + locationR16 13177 *
        radiusPolynomialRoot16 (d.f0 13177 166) (d.f1 13177 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13177 : ℝ) ^ 8 * (mA 13177 : ℝ) ^ 8 *
        ((((2089570793 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2089570793 / 500000000000000000)) * ((1394232343 / 1000000000000000000)) * (126 / 100) +
          2 * (((1394232343 / 1000000000000000000)) ^ 2 + 2 * ((2089570793 / 500000000000000000)) * ((167552143 / 500000000000000000))) +
          6 * ((1394232343 / 1000000000000000000)) * ((167552143 / 500000000000000000)) * (126 / 100) + 8 * ((167552143 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13177) *
          (32 * (((2089570793 / 500000000000000000) : ℝ) + (1394232343 / 1000000000000000000) + (167552143 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13177 : ℝ) ^ 16 *
      (d.w0 13177 166 + d.w1 13177 166 * √(π / 2) + 2 * d.w2 13177 166 +
        energyR16 13177 * radiusPolynomialRoot16 (d.w0 13177 166) (d.w1 13177 166)
          (d.w2 13177 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13177 : ℝ) ^ 16 *
        (((820613537 / 50000000000000000000) : ℝ) + ((1167701721 / 100000000000000000000)) * (126 / 100) + 2 * ((213324069 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13177) *
          (32 * (((820613537 / 50000000000000000000) : ℝ) + (1167701721 / 100000000000000000000) + (213324069 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13177

/-! A coarse bound on the actual paper statistics constant at dimension 13178. -/
namespace BstLean.Part266.Row13178
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13176 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13176 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13176 128 ≤ (13430 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13430 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13178) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13178 : ℕ))
    (by norm_num : (13178 : ℕ) ≤ 16384)
  have ht : paperTail256 13178 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13178 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13178 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13178 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13178 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13178 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13176 128 * √(2 / (13178 : ℝ)) *
      (√(13178 : ℝ) + paperT0 13178 + paperTail256 13178) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13178 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13178 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13178 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13176 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13176 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13178 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13178

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13178
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13178 (61 / 100) 166 (17 / (100 * 13178)) (26 / (10 * 13178)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13178 (61 / 100) 166 (17 / (100 * 13178)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (3332401 / 781250000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1294725553 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (950587089 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13178 / 13178 * (61 / 100)) ^ 4 * inverseRadius8 (13178 - 1) /
            envelopeGap 13178 (61 / 100) 166 (17 / (100 * 13178)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13178

namespace BstLean.Part266.Row13178
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13178 166 ≤ (4178347803 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13178 166 ≤ (1393967621 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (167520343 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13178 166 ≤ (1640853261 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13178 166 ≤ (233487161 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 13178 166 ≤ (106637753 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (3332401 / 781250000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (3332401 / 781250000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1294725553 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (950587089 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3591697 / 1000000000) : ℝ) ≤ √(17 / (100 * 13178) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13178) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (82612089 / 40000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (17991147497 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13178) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13178) ≤ (26829063 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13178) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13178 * (166 : ℝ) ^ 2 + 26 / (10 * 13178) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13178) : ℝ)) (tA 13178 * 166 ^ 2 + 26 / (10 * 13178)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3591697 / 1000000000))) * ((3332401 / 781250000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3591697 / 1000000000)) ^ 3) * ((1294725553 / 1000000000000000000000000))) + ((950587089 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3591697 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13178) : ℝ)) d.D d.V d.P (√(tA 13178) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3591697 / 1000000000)) ^ 2 * (((82612089 / 40000000000000)) * ((17991147497 / 500000000000000000)))) + ((950587089 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13178) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3591697 / 1000000000)) * ((3332401 / 781250000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13178) : ℝ)) (tA 13178 * 166 ^ 2 + 26 / (10 * 13178)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((3332401 / 781250000000000000) : ℝ) + (24198 / 100000) / (2 * ((3591697 / 1000000000)) ^ 2) * ((1294725553 / 1000000000000000000000000)) + ((950587089 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13178) : ℝ)) (√(26 / (10 * 13178) : ℝ)) d.D d.V d.P (√(tA 13178) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3591697 / 1000000000)) * (((82612089 / 40000000000000)) * ((17991147497 / 500000000000000000))) + ((950587089 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13178) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((3332401 / 781250000000000000) : ℝ) + ((950587089 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13178

namespace BstLean.Part266.Row13178
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13178 166 ∧
    0 ≤ (tableEnvelope C).f1 13178 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13178 166 ∧
    0 ≤ (tableEnvelope C).w1 13178 166 ∧ 0 ≤ (tableEnvelope C).w2 13178 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13178 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13178 166 ∧ 0 ≤ d.f1 13178 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13178 166 ∧ 0 ≤ d.w1 13178 166 ∧ 0 ≤ d.w2 13178 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13178 ≤ 2 * (228 / 100 : ℝ) / 13178 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13178 ≤ 2 * (370 / 100 : ℝ) / 13178 := by
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
    (completeRAData (tableEnvelope C) 13178 166).locationBound 13178 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13178 166).energyBound 13178 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13178 166) (d.f1 13178 166) d.f2 ≤
      32 * (((4178347803 / 1000000000000000000) : ℝ) + (1393967621 / 1000000000000000000) + (167520343 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13178 166) (d.w1 13178 166)
      (d.w2 13178 166) ≤
      32 * (((1640853261 / 100000000000000000000) : ℝ) + (233487161 / 20000000000000000000) + (106637753 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13178 166) (d.f1 13178 166) d.f2 ≤
      ((4178347803 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4178347803 / 1000000000000000000)) * ((1393967621 / 1000000000000000000)) * (126 / 100) +
      2 * (((1393967621 / 1000000000000000000)) ^ 2 + 2 * ((4178347803 / 1000000000000000000)) * ((167520343 / 500000000000000000))) +
      6 * ((1393967621 / 1000000000000000000)) * ((167520343 / 500000000000000000)) * (126 / 100) + 8 * ((167520343 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13178 166) (d.f1 13178 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13178 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13178 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13178 166) (d.f1 13178 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13178 166) (d.w1 13178 166) (d.w2 13178 166)
  have hwexpr0 : 0 ≤ d.w0 13178 166 + d.w1 13178 166 * √(π / 2) +
      2 * d.w2 13178 166 + energyR16 13178 *
      radiusPolynomialRoot16 (d.w0 13178 166) (d.w1 13178 166) (d.w2 13178 166) := by
    positivity
  constructor
  · change (13178 : ℝ) ^ 8 * (mA 13178 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13178 166) (d.f1 13178 166) d.f2 + locationR16 13178 *
        radiusPolynomialRoot16 (d.f0 13178 166) (d.f1 13178 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13178 : ℝ) ^ 8 * (mA 13178 : ℝ) ^ 8 *
        ((((4178347803 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4178347803 / 1000000000000000000)) * ((1393967621 / 1000000000000000000)) * (126 / 100) +
          2 * (((1393967621 / 1000000000000000000)) ^ 2 + 2 * ((4178347803 / 1000000000000000000)) * ((167520343 / 500000000000000000))) +
          6 * ((1393967621 / 1000000000000000000)) * ((167520343 / 500000000000000000)) * (126 / 100) + 8 * ((167520343 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13178) *
          (32 * (((4178347803 / 1000000000000000000) : ℝ) + (1393967621 / 1000000000000000000) + (167520343 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13178 : ℝ) ^ 16 *
      (d.w0 13178 166 + d.w1 13178 166 * √(π / 2) + 2 * d.w2 13178 166 +
        energyR16 13178 * radiusPolynomialRoot16 (d.w0 13178 166) (d.w1 13178 166)
          (d.w2 13178 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13178 : ℝ) ^ 16 *
        (((1640853261 / 100000000000000000000) : ℝ) + ((233487161 / 20000000000000000000)) * (126 / 100) + 2 * ((106637753 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13178) *
          (32 * (((1640853261 / 100000000000000000000) : ℝ) + (233487161 / 20000000000000000000) + (106637753 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13178

/-! A coarse bound on the actual paper statistics constant at dimension 13179. -/
namespace BstLean.Part266.Row13179
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13177 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13177 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13177 128 ≤ (13431 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13431 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13179) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13179 : ℕ))
    (by norm_num : (13179 : ℕ) ≤ 16384)
  have ht : paperTail256 13179 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13179 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13179 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13179 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13179 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13179 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13177 128 * √(2 / (13179 : ℝ)) *
      (√(13179 : ℝ) + paperT0 13179 + paperTail256 13179) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13179 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13179 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13179 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13177 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13177 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13179 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13179

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13179
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13179 (61 / 100) 166 (17 / (100 * 13179)) (26 / (10 * 13179)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13179 (61 / 100) 166 (17 / (100 * 13179)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (426450233 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1294332617 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3800019203 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13179 / 13179 * (61 / 100)) ^ 4 * inverseRadius8 (13179 - 1) /
            envelopeGap 13179 (61 / 100) 166 (17 / (100 * 13179)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13179

namespace BstLean.Part266.Row13179
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13179 166 ≤ (2088778821 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13179 166 ≤ (696851879 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (167488599 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13179 166 ≤ (6561921 / 400000000000000000)
  w1 : (tableEnvelope C).w1 13179 166 ≤ (11671703 / 1000000000000000000)
  w2 : (tableEnvelope C).w2 13179 166 ≤ (85290783 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (426450233 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (426450233 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1294332617 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3800019203 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((89789 / 25000000) : ℝ) ≤ √(17 / (100 * 13179) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13179) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (41301343 / 20000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (719536689 / 20000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13179) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13179) ≤ (107308109 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13179) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13179 * (166 : ℝ) ^ 2 + 26 / (10 * 13179) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13179) : ℝ)) (tA 13179 * 166 ^ 2 + 26 / (10 * 13179)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((89789 / 25000000))) * ((426450233 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((89789 / 25000000)) ^ 3) * ((1294332617 / 1000000000000000000000000))) + ((3800019203 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((89789 / 25000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13179) : ℝ)) d.D d.V d.P (√(tA 13179) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((89789 / 25000000)) ^ 2 * (((41301343 / 20000000000000)) * ((719536689 / 20000000000000000)))) + ((3800019203 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13179) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((89789 / 25000000)) * ((426450233 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13179) : ℝ)) (tA 13179 * 166 ^ 2 + 26 / (10 * 13179)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((426450233 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((89789 / 25000000)) ^ 2) * ((1294332617 / 1000000000000000000000000)) + ((3800019203 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13179) : ℝ)) (√(26 / (10 * 13179) : ℝ)) d.D d.V d.P (√(tA 13179) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((89789 / 25000000)) * (((41301343 / 20000000000000)) * ((719536689 / 20000000000000000))) + ((3800019203 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13179) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((426450233 / 100000000000000000000) : ℝ) + ((3800019203 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13179

namespace BstLean.Part266.Row13179
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13179 166 ∧
    0 ≤ (tableEnvelope C).f1 13179 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13179 166 ∧
    0 ≤ (tableEnvelope C).w1 13179 166 ∧ 0 ≤ (tableEnvelope C).w2 13179 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13179 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13179 166 ∧ 0 ≤ d.f1 13179 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13179 166 ∧ 0 ≤ d.w1 13179 166 ∧ 0 ≤ d.w2 13179 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13179 ≤ 2 * (228 / 100 : ℝ) / 13179 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13179 ≤ 2 * (370 / 100 : ℝ) / 13179 := by
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
    (completeRAData (tableEnvelope C) 13179 166).locationBound 13179 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13179 166).energyBound 13179 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13179 166) (d.f1 13179 166) d.f2 ≤
      32 * (((2088778821 / 500000000000000000) : ℝ) + (696851879 / 500000000000000000) + (167488599 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13179 166) (d.w1 13179 166)
      (d.w2 13179 166) ≤
      32 * (((6561921 / 400000000000000000) : ℝ) + (11671703 / 1000000000000000000) + (85290783 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13179 166) (d.f1 13179 166) d.f2 ≤
      ((2088778821 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2088778821 / 500000000000000000)) * ((696851879 / 500000000000000000)) * (126 / 100) +
      2 * (((696851879 / 500000000000000000)) ^ 2 + 2 * ((2088778821 / 500000000000000000)) * ((167488599 / 500000000000000000))) +
      6 * ((696851879 / 500000000000000000)) * ((167488599 / 500000000000000000)) * (126 / 100) + 8 * ((167488599 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13179 166) (d.f1 13179 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13179 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13179 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13179 166) (d.f1 13179 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13179 166) (d.w1 13179 166) (d.w2 13179 166)
  have hwexpr0 : 0 ≤ d.w0 13179 166 + d.w1 13179 166 * √(π / 2) +
      2 * d.w2 13179 166 + energyR16 13179 *
      radiusPolynomialRoot16 (d.w0 13179 166) (d.w1 13179 166) (d.w2 13179 166) := by
    positivity
  constructor
  · change (13179 : ℝ) ^ 8 * (mA 13179 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13179 166) (d.f1 13179 166) d.f2 + locationR16 13179 *
        radiusPolynomialRoot16 (d.f0 13179 166) (d.f1 13179 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13179 : ℝ) ^ 8 * (mA 13179 : ℝ) ^ 8 *
        ((((2088778821 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2088778821 / 500000000000000000)) * ((696851879 / 500000000000000000)) * (126 / 100) +
          2 * (((696851879 / 500000000000000000)) ^ 2 + 2 * ((2088778821 / 500000000000000000)) * ((167488599 / 500000000000000000))) +
          6 * ((696851879 / 500000000000000000)) * ((167488599 / 500000000000000000)) * (126 / 100) + 8 * ((167488599 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13179) *
          (32 * (((2088778821 / 500000000000000000) : ℝ) + (696851879 / 500000000000000000) + (167488599 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13179 : ℝ) ^ 16 *
      (d.w0 13179 166 + d.w1 13179 166 * √(π / 2) + 2 * d.w2 13179 166 +
        energyR16 13179 * radiusPolynomialRoot16 (d.w0 13179 166) (d.w1 13179 166)
          (d.w2 13179 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13179 : ℝ) ^ 16 *
        (((6561921 / 400000000000000000) : ℝ) + ((11671703 / 1000000000000000000)) * (126 / 100) + 2 * ((85290783 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13179) *
          (32 * (((6561921 / 400000000000000000) : ℝ) + (11671703 / 1000000000000000000) + (85290783 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13179

/-! A coarse bound on the actual paper statistics constant at dimension 13180. -/
namespace BstLean.Part266.Row13180
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13178 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13178 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13178 128 ≤ (13432 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13432 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13180) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13180 : ℕ))
    (by norm_num : (13180 : ℕ) ≤ 16384)
  have ht : paperTail256 13180 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13180 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13180 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13180 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13180 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13180 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13178 128 * √(2 / (13180 : ℝ)) *
      (√(13180 : ℝ) + paperT0 13180 + paperTail256 13180) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13180 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13180 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13180 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13178 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13178 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13180 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13180

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13180
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13180 (61 / 100) 166 (17 / (100 * 13180)) (26 / (10 * 13180)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13180 (61 / 100) 166 (17 / (100 * 13180)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (26647073 / 6250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1293939829 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1898845829 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13180 / 13180 * (61 / 100)) ^ 4 * inverseRadius8 (13180 - 1) /
            envelopeGap 13180 (61 / 100) 166 (17 / (100 * 13180)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13180

namespace BstLean.Part266.Row13180
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13180 166 ≤ (4176764383 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13180 166 ≤ (1741799 / 1250000000000000)
  f2 : (tableEnvelope C).f2 ≤ (83728409 / 250000000000000000)
  w0 : (tableEnvelope C).w0 13180 166 ≤ (328021337 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 13180 166 ≤ (291726139 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 13180 166 ≤ (426356847 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (26647073 / 6250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (26647073 / 6250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1293939829 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1898845829 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((14029 / 3906250) : ℝ) ≤ √(17 / (100 * 13180) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13180) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (51620803 / 25000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (17985687567 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13180) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13180) ≤ (107299967 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13180) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13180 * (166 : ℝ) ^ 2 + 26 / (10 * 13180) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13180) : ℝ)) (tA 13180 * 166 ^ 2 + 26 / (10 * 13180)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((14029 / 3906250))) * ((26647073 / 6250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((14029 / 3906250)) ^ 3) * ((1293939829 / 1000000000000000000000000))) + ((1898845829 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((14029 / 3906250)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13180) : ℝ)) d.D d.V d.P (√(tA 13180) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((14029 / 3906250)) ^ 2 * (((51620803 / 25000000000000)) * ((17985687567 / 500000000000000000)))) + ((1898845829 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13180) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((14029 / 3906250)) * ((26647073 / 6250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13180) : ℝ)) (tA 13180 * 166 ^ 2 + 26 / (10 * 13180)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((26647073 / 6250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((14029 / 3906250)) ^ 2) * ((1293939829 / 1000000000000000000000000)) + ((1898845829 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13180) : ℝ)) (√(26 / (10 * 13180) : ℝ)) d.D d.V d.P (√(tA 13180) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((14029 / 3906250)) * (((51620803 / 25000000000000)) * ((17985687567 / 500000000000000000))) + ((1898845829 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13180) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((26647073 / 6250000000000000000) : ℝ) + ((1898845829 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13180

namespace BstLean.Part266.Row13180
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13180 166 ∧
    0 ≤ (tableEnvelope C).f1 13180 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13180 166 ∧
    0 ≤ (tableEnvelope C).w1 13180 166 ∧ 0 ≤ (tableEnvelope C).w2 13180 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13180 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13180 166 ∧ 0 ≤ d.f1 13180 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13180 166 ∧ 0 ≤ d.w1 13180 166 ∧ 0 ≤ d.w2 13180 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13180 ≤ 2 * (228 / 100 : ℝ) / 13180 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13180 ≤ 2 * (370 / 100 : ℝ) / 13180 := by
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
    (completeRAData (tableEnvelope C) 13180 166).locationBound 13180 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13180 166).energyBound 13180 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13180 166) (d.f1 13180 166) d.f2 ≤
      32 * (((4176764383 / 1000000000000000000) : ℝ) + (1741799 / 1250000000000000) + (83728409 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13180 166) (d.w1 13180 166)
      (d.w2 13180 166) ≤
      32 * (((328021337 / 20000000000000000000) : ℝ) + (291726139 / 25000000000000000000) + (426356847 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13180 166) (d.f1 13180 166) d.f2 ≤
      ((4176764383 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4176764383 / 1000000000000000000)) * ((1741799 / 1250000000000000)) * (126 / 100) +
      2 * (((1741799 / 1250000000000000)) ^ 2 + 2 * ((4176764383 / 1000000000000000000)) * ((83728409 / 250000000000000000))) +
      6 * ((1741799 / 1250000000000000)) * ((83728409 / 250000000000000000)) * (126 / 100) + 8 * ((83728409 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13180 166) (d.f1 13180 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13180 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13180 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13180 166) (d.f1 13180 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13180 166) (d.w1 13180 166) (d.w2 13180 166)
  have hwexpr0 : 0 ≤ d.w0 13180 166 + d.w1 13180 166 * √(π / 2) +
      2 * d.w2 13180 166 + energyR16 13180 *
      radiusPolynomialRoot16 (d.w0 13180 166) (d.w1 13180 166) (d.w2 13180 166) := by
    positivity
  constructor
  · change (13180 : ℝ) ^ 8 * (mA 13180 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13180 166) (d.f1 13180 166) d.f2 + locationR16 13180 *
        radiusPolynomialRoot16 (d.f0 13180 166) (d.f1 13180 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13180 : ℝ) ^ 8 * (mA 13180 : ℝ) ^ 8 *
        ((((4176764383 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4176764383 / 1000000000000000000)) * ((1741799 / 1250000000000000)) * (126 / 100) +
          2 * (((1741799 / 1250000000000000)) ^ 2 + 2 * ((4176764383 / 1000000000000000000)) * ((83728409 / 250000000000000000))) +
          6 * ((1741799 / 1250000000000000)) * ((83728409 / 250000000000000000)) * (126 / 100) + 8 * ((83728409 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13180) *
          (32 * (((4176764383 / 1000000000000000000) : ℝ) + (1741799 / 1250000000000000) + (83728409 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13180 : ℝ) ^ 16 *
      (d.w0 13180 166 + d.w1 13180 166 * √(π / 2) + 2 * d.w2 13180 166 +
        energyR16 13180 * radiusPolynomialRoot16 (d.w0 13180 166) (d.w1 13180 166)
          (d.w2 13180 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13180 : ℝ) ^ 16 *
        (((328021337 / 20000000000000000000) : ℝ) + ((291726139 / 25000000000000000000)) * (126 / 100) + 2 * ((426356847 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13180) *
          (32 * (((328021337 / 20000000000000000000) : ℝ) + (291726139 / 25000000000000000000) + (426356847 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13180

/-! A coarse bound on the actual paper statistics constant at dimension 13181. -/
namespace BstLean.Part266.Row13181
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13179 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13179 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13179 128 ≤ (13433 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13433 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13181) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13181 : ℕ))
    (by norm_num : (13181 : ℕ) ≤ 16384)
  have ht : paperTail256 13181 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13181 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13181 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13181 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13181 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13181 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13179 128 * √(2 / (13181 : ℝ)) *
      (√(13181 : ℝ) + paperT0 13181 + paperTail256 13181) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13181 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13181 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13181 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13179 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13179 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13181 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13181

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13181
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13181 (61 / 100) 166 (17 / (100 * 13181)) (26 / (10 * 13181)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13181 (61 / 100) 166 (17 / (100 * 13181)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (106564033 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1293547191 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3795365717 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13181 / 13181 * (61 / 100)) ^ 4 * inverseRadius8 (13181 - 1) /
            envelopeGap 13181 (61 / 100) 166 (17 / (100 * 13181)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13181

namespace BstLean.Part266.Row13181
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13181 166 ≤ (417597139 / 100000000000000000)
  f1 : (tableEnvelope C).f1 13181 166 ≤ (55726989 / 40000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (334850091 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13181 166 ≤ (327946649 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 13181 166 ≤ (1166638897 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13181 166 ≤ (426259809 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (106564033 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (106564033 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1293547191 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3795365717 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((448911 / 125000000) : ℝ) ≤ √(17 / (100 * 13181) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13181) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2064597133 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1438636683 / 40000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13181) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13181) ≤ (107291827 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13181) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13181 * (166 : ℝ) ^ 2 + 26 / (10 * 13181) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13181) : ℝ)) (tA 13181 * 166 ^ 2 + 26 / (10 * 13181)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((448911 / 125000000))) * ((106564033 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((448911 / 125000000)) ^ 3) * ((1293547191 / 1000000000000000000000000))) + ((3795365717 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((448911 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13181) : ℝ)) d.D d.V d.P (√(tA 13181) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((448911 / 125000000)) ^ 2 * (((2064597133 / 1000000000000000)) * ((1438636683 / 40000000000000000)))) + ((3795365717 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13181) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((448911 / 125000000)) * ((106564033 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13181) : ℝ)) (tA 13181 * 166 ^ 2 + 26 / (10 * 13181)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((106564033 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((448911 / 125000000)) ^ 2) * ((1293547191 / 1000000000000000000000000)) + ((3795365717 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13181) : ℝ)) (√(26 / (10 * 13181) : ℝ)) d.D d.V d.P (√(tA 13181) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((448911 / 125000000)) * (((2064597133 / 1000000000000000)) * ((1438636683 / 40000000000000000))) + ((3795365717 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13181) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((106564033 / 25000000000000000000) : ℝ) + ((3795365717 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13181

namespace BstLean.Part266.Row13181
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13181 166 ∧
    0 ≤ (tableEnvelope C).f1 13181 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13181 166 ∧
    0 ≤ (tableEnvelope C).w1 13181 166 ∧ 0 ≤ (tableEnvelope C).w2 13181 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13181 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13181 166 ∧ 0 ≤ d.f1 13181 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13181 166 ∧ 0 ≤ d.w1 13181 166 ∧ 0 ≤ d.w2 13181 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13181 ≤ 2 * (228 / 100 : ℝ) / 13181 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13181 ≤ 2 * (370 / 100 : ℝ) / 13181 := by
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
    (completeRAData (tableEnvelope C) 13181 166).locationBound 13181 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13181 166).energyBound 13181 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13181 166) (d.f1 13181 166) d.f2 ≤
      32 * (((417597139 / 100000000000000000) : ℝ) + (55726989 / 40000000000000000) + (334850091 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13181 166) (d.w1 13181 166)
      (d.w2 13181 166) ≤
      32 * (((327946649 / 20000000000000000000) : ℝ) + (1166638897 / 100000000000000000000) + (426259809 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13181 166) (d.f1 13181 166) d.f2 ≤
      ((417597139 / 100000000000000000) : ℝ) ^ 2 + 2 * ((417597139 / 100000000000000000)) * ((55726989 / 40000000000000000)) * (126 / 100) +
      2 * (((55726989 / 40000000000000000)) ^ 2 + 2 * ((417597139 / 100000000000000000)) * ((334850091 / 1000000000000000000))) +
      6 * ((55726989 / 40000000000000000)) * ((334850091 / 1000000000000000000)) * (126 / 100) + 8 * ((334850091 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13181 166) (d.f1 13181 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13181 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13181 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13181 166) (d.f1 13181 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13181 166) (d.w1 13181 166) (d.w2 13181 166)
  have hwexpr0 : 0 ≤ d.w0 13181 166 + d.w1 13181 166 * √(π / 2) +
      2 * d.w2 13181 166 + energyR16 13181 *
      radiusPolynomialRoot16 (d.w0 13181 166) (d.w1 13181 166) (d.w2 13181 166) := by
    positivity
  constructor
  · change (13181 : ℝ) ^ 8 * (mA 13181 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13181 166) (d.f1 13181 166) d.f2 + locationR16 13181 *
        radiusPolynomialRoot16 (d.f0 13181 166) (d.f1 13181 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13181 : ℝ) ^ 8 * (mA 13181 : ℝ) ^ 8 *
        ((((417597139 / 100000000000000000) : ℝ) ^ 2 + 2 * ((417597139 / 100000000000000000)) * ((55726989 / 40000000000000000)) * (126 / 100) +
          2 * (((55726989 / 40000000000000000)) ^ 2 + 2 * ((417597139 / 100000000000000000)) * ((334850091 / 1000000000000000000))) +
          6 * ((55726989 / 40000000000000000)) * ((334850091 / 1000000000000000000)) * (126 / 100) + 8 * ((334850091 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13181) *
          (32 * (((417597139 / 100000000000000000) : ℝ) + (55726989 / 40000000000000000) + (334850091 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13181 : ℝ) ^ 16 *
      (d.w0 13181 166 + d.w1 13181 166 * √(π / 2) + 2 * d.w2 13181 166 +
        energyR16 13181 * radiusPolynomialRoot16 (d.w0 13181 166) (d.w1 13181 166)
          (d.w2 13181 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13181 : ℝ) ^ 16 *
        (((327946649 / 20000000000000000000) : ℝ) + ((1166638897 / 100000000000000000000)) * (126 / 100) + 2 * ((426259809 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13181) *
          (32 * (((327946649 / 20000000000000000000) : ℝ) + (1166638897 / 100000000000000000000) + (426259809 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13181

/-! A coarse bound on the actual paper statistics constant at dimension 13182. -/
namespace BstLean.Part266.Row13182
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13180 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13180 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13180 128 ≤ (13434 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13434 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13182) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13182 : ℕ))
    (by norm_num : (13182 : ℕ) ≤ 16384)
  have ht : paperTail256 13182 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13182 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13182 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13182 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13182 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13182 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13180 128 * √(2 / (13182 : ℝ)) *
      (√(13182 : ℝ) + paperT0 13182 + paperTail256 13182) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13182 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13182 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13182 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13180 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13180 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13182 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13182

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13182
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13182 (61 / 100) 166 (17 / (100 * 13182)) (26 / (10 * 13182)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13182 (61 / 100) 166 (17 / (100 * 13182)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (213079563 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1293154701 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3793041381 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13182 / 13182 * (61 / 100)) ^ 4 * inverseRadius8 (13182 - 1) /
            envelopeGap 13182 (61 / 100) 166 (17 / (100 * 13182)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13182

namespace BstLean.Part266.Row13182
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13182 166 ≤ (4175178657 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13182 166 ≤ (1392910333 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (66957313 / 200000000000000000)
  w0 : (tableEnvelope C).w0 13182 166 ≤ (204919991 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 13182 166 ≤ (46654933 / 4000000000000000000)
  w2 : (tableEnvelope C).w2 13182 166 ≤ (426162801 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (213079563 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (213079563 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1293154701 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3793041381 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((224447 / 62500000) : ℝ) ≤ √(17 / (100 * 13182) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13182) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2064362193 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7192092049 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13182) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13182) ≤ (13410461 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13182) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13182 * (166 : ℝ) ^ 2 + 26 / (10 * 13182) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13182) : ℝ)) (tA 13182 * 166 ^ 2 + 26 / (10 * 13182)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((224447 / 62500000))) * ((213079563 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((224447 / 62500000)) ^ 3) * ((1293154701 / 1000000000000000000000000))) + ((3793041381 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((224447 / 62500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13182) : ℝ)) d.D d.V d.P (√(tA 13182) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((224447 / 62500000)) ^ 2 * (((2064362193 / 1000000000000000)) * ((7192092049 / 200000000000000000)))) + ((3793041381 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13182) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((224447 / 62500000)) * ((213079563 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13182) : ℝ)) (tA 13182 * 166 ^ 2 + 26 / (10 * 13182)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((213079563 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((224447 / 62500000)) ^ 2) * ((1293154701 / 1000000000000000000000000)) + ((3793041381 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13182) : ℝ)) (√(26 / (10 * 13182) : ℝ)) d.D d.V d.P (√(tA 13182) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((224447 / 62500000)) * (((2064362193 / 1000000000000000)) * ((7192092049 / 200000000000000000))) + ((3793041381 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13182) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((213079563 / 50000000000000000000) : ℝ) + ((3793041381 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13182

namespace BstLean.Part266.Row13182
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13182 166 ∧
    0 ≤ (tableEnvelope C).f1 13182 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13182 166 ∧
    0 ≤ (tableEnvelope C).w1 13182 166 ∧ 0 ≤ (tableEnvelope C).w2 13182 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13182 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13182 166 ∧ 0 ≤ d.f1 13182 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13182 166 ∧ 0 ≤ d.w1 13182 166 ∧ 0 ≤ d.w2 13182 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13182 ≤ 2 * (228 / 100 : ℝ) / 13182 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13182 ≤ 2 * (370 / 100 : ℝ) / 13182 := by
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
    (completeRAData (tableEnvelope C) 13182 166).locationBound 13182 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13182 166).energyBound 13182 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13182 166) (d.f1 13182 166) d.f2 ≤
      32 * (((4175178657 / 1000000000000000000) : ℝ) + (1392910333 / 1000000000000000000) + (66957313 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13182 166) (d.w1 13182 166)
      (d.w2 13182 166) ≤
      32 * (((204919991 / 12500000000000000000) : ℝ) + (46654933 / 4000000000000000000) + (426162801 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13182 166) (d.f1 13182 166) d.f2 ≤
      ((4175178657 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4175178657 / 1000000000000000000)) * ((1392910333 / 1000000000000000000)) * (126 / 100) +
      2 * (((1392910333 / 1000000000000000000)) ^ 2 + 2 * ((4175178657 / 1000000000000000000)) * ((66957313 / 200000000000000000))) +
      6 * ((1392910333 / 1000000000000000000)) * ((66957313 / 200000000000000000)) * (126 / 100) + 8 * ((66957313 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13182 166) (d.f1 13182 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13182 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13182 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13182 166) (d.f1 13182 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13182 166) (d.w1 13182 166) (d.w2 13182 166)
  have hwexpr0 : 0 ≤ d.w0 13182 166 + d.w1 13182 166 * √(π / 2) +
      2 * d.w2 13182 166 + energyR16 13182 *
      radiusPolynomialRoot16 (d.w0 13182 166) (d.w1 13182 166) (d.w2 13182 166) := by
    positivity
  constructor
  · change (13182 : ℝ) ^ 8 * (mA 13182 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13182 166) (d.f1 13182 166) d.f2 + locationR16 13182 *
        radiusPolynomialRoot16 (d.f0 13182 166) (d.f1 13182 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13182 : ℝ) ^ 8 * (mA 13182 : ℝ) ^ 8 *
        ((((4175178657 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4175178657 / 1000000000000000000)) * ((1392910333 / 1000000000000000000)) * (126 / 100) +
          2 * (((1392910333 / 1000000000000000000)) ^ 2 + 2 * ((4175178657 / 1000000000000000000)) * ((66957313 / 200000000000000000))) +
          6 * ((1392910333 / 1000000000000000000)) * ((66957313 / 200000000000000000)) * (126 / 100) + 8 * ((66957313 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13182) *
          (32 * (((4175178657 / 1000000000000000000) : ℝ) + (1392910333 / 1000000000000000000) + (66957313 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13182 : ℝ) ^ 16 *
      (d.w0 13182 166 + d.w1 13182 166 * √(π / 2) + 2 * d.w2 13182 166 +
        energyR16 13182 * radiusPolynomialRoot16 (d.w0 13182 166) (d.w1 13182 166)
          (d.w2 13182 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13182 : ℝ) ^ 16 *
        (((204919991 / 12500000000000000000) : ℝ) + ((46654933 / 4000000000000000000)) * (126 / 100) + 2 * ((426162801 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13182) *
          (32 * (((204919991 / 12500000000000000000) : ℝ) + (46654933 / 4000000000000000000) + (426162801 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13182

/-! A coarse bound on the actual paper statistics constant at dimension 13183. -/
namespace BstLean.Part266.Row13183
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13181 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13181 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13181 128 ≤ (13435 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13435 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13183) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13183 : ℕ))
    (by norm_num : (13183 : ℕ) ≤ 16384)
  have ht : paperTail256 13183 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13183 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13183 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13183 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13183 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13183 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13181 128 * √(2 / (13183 : ℝ)) *
      (√(13183 : ℝ) + paperT0 13183 + paperTail256 13183) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13183 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13183 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13183 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13181 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13181 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13183 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13183

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13183
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13183 (61 / 100) 166 (17 / (100 * 13183)) (26 / (10 * 13183)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13183 (61 / 100) 166 (17 / (100 * 13183)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (426062149 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1292762361 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3790718647 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13183 / 13183 * (61 / 100)) ^ 4 * inverseRadius8 (13183 - 1) /
            envelopeGap 13183 (61 / 100) 166 (17 / (100 * 13183)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13183

namespace BstLean.Part266.Row13183
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13183 166 ≤ (834877909 / 200000000000000000)
  f1 : (tableEnvelope C).f1 13183 166 ≤ (696323399 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (6694463 / 20000000000000000)
  w0 : (tableEnvelope C).w0 13183 166 ≤ (409746853 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 13183 166 ≤ (583054081 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13183 166 ≤ (213032911 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (426062149 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (426062149 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1292762361 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3790718647 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((718203 / 200000000) : ℝ) ≤ √(17 / (100 * 13183) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13183) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (32251989 / 15625000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (35955004673 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13183) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13183) ≤ (107275549 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13183) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13183 * (166 : ℝ) ^ 2 + 26 / (10 * 13183) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13183) : ℝ)) (tA 13183 * 166 ^ 2 + 26 / (10 * 13183)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((718203 / 200000000))) * ((426062149 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((718203 / 200000000)) ^ 3) * ((1292762361 / 1000000000000000000000000))) + ((3790718647 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((718203 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13183) : ℝ)) d.D d.V d.P (√(tA 13183) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((718203 / 200000000)) ^ 2 * (((32251989 / 15625000000000)) * ((35955004673 / 1000000000000000000)))) + ((3790718647 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13183) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((718203 / 200000000)) * ((426062149 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13183) : ℝ)) (tA 13183 * 166 ^ 2 + 26 / (10 * 13183)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((426062149 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((718203 / 200000000)) ^ 2) * ((1292762361 / 1000000000000000000000000)) + ((3790718647 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13183) : ℝ)) (√(26 / (10 * 13183) : ℝ)) d.D d.V d.P (√(tA 13183) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((718203 / 200000000)) * (((32251989 / 15625000000000)) * ((35955004673 / 1000000000000000000))) + ((3790718647 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13183) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((426062149 / 100000000000000000000) : ℝ) + ((3790718647 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13183

namespace BstLean.Part266.Row13183
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13183 166 ∧
    0 ≤ (tableEnvelope C).f1 13183 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13183 166 ∧
    0 ≤ (tableEnvelope C).w1 13183 166 ∧ 0 ≤ (tableEnvelope C).w2 13183 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13183 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13183 166 ∧ 0 ≤ d.f1 13183 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13183 166 ∧ 0 ≤ d.w1 13183 166 ∧ 0 ≤ d.w2 13183 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13183 ≤ 2 * (228 / 100 : ℝ) / 13183 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13183 ≤ 2 * (370 / 100 : ℝ) / 13183 := by
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
    (completeRAData (tableEnvelope C) 13183 166).locationBound 13183 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13183 166).energyBound 13183 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13183 166) (d.f1 13183 166) d.f2 ≤
      32 * (((834877909 / 200000000000000000) : ℝ) + (696323399 / 500000000000000000) + (6694463 / 20000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13183 166) (d.w1 13183 166)
      (d.w2 13183 166) ≤
      32 * (((409746853 / 25000000000000000000) : ℝ) + (583054081 / 50000000000000000000) + (213032911 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13183 166) (d.f1 13183 166) d.f2 ≤
      ((834877909 / 200000000000000000) : ℝ) ^ 2 + 2 * ((834877909 / 200000000000000000)) * ((696323399 / 500000000000000000)) * (126 / 100) +
      2 * (((696323399 / 500000000000000000)) ^ 2 + 2 * ((834877909 / 200000000000000000)) * ((6694463 / 20000000000000000))) +
      6 * ((696323399 / 500000000000000000)) * ((6694463 / 20000000000000000)) * (126 / 100) + 8 * ((6694463 / 20000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13183 166) (d.f1 13183 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13183 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13183 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13183 166) (d.f1 13183 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13183 166) (d.w1 13183 166) (d.w2 13183 166)
  have hwexpr0 : 0 ≤ d.w0 13183 166 + d.w1 13183 166 * √(π / 2) +
      2 * d.w2 13183 166 + energyR16 13183 *
      radiusPolynomialRoot16 (d.w0 13183 166) (d.w1 13183 166) (d.w2 13183 166) := by
    positivity
  constructor
  · change (13183 : ℝ) ^ 8 * (mA 13183 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13183 166) (d.f1 13183 166) d.f2 + locationR16 13183 *
        radiusPolynomialRoot16 (d.f0 13183 166) (d.f1 13183 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13183 : ℝ) ^ 8 * (mA 13183 : ℝ) ^ 8 *
        ((((834877909 / 200000000000000000) : ℝ) ^ 2 + 2 * ((834877909 / 200000000000000000)) * ((696323399 / 500000000000000000)) * (126 / 100) +
          2 * (((696323399 / 500000000000000000)) ^ 2 + 2 * ((834877909 / 200000000000000000)) * ((6694463 / 20000000000000000))) +
          6 * ((696323399 / 500000000000000000)) * ((6694463 / 20000000000000000)) * (126 / 100) + 8 * ((6694463 / 20000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13183) *
          (32 * (((834877909 / 200000000000000000) : ℝ) + (696323399 / 500000000000000000) + (6694463 / 20000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13183 : ℝ) ^ 16 *
      (d.w0 13183 166 + d.w1 13183 166 * √(π / 2) + 2 * d.w2 13183 166 +
        energyR16 13183 * radiusPolynomialRoot16 (d.w0 13183 166) (d.w1 13183 166)
          (d.w2 13183 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13183 : ℝ) ^ 16 *
        (((409746853 / 25000000000000000000) : ℝ) + ((583054081 / 50000000000000000000)) * (126 / 100) + 2 * ((213032911 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13183) *
          (32 * (((409746853 / 25000000000000000000) : ℝ) + (583054081 / 50000000000000000000) + (213032911 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13183

/-! A coarse bound on the actual paper statistics constant at dimension 13184. -/
namespace BstLean.Part266.Row13184
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13182 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13182 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13182 128 ≤ (13436 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13436 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13184) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13184 : ℕ))
    (by norm_num : (13184 : ℕ) ≤ 16384)
  have ht : paperTail256 13184 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13184 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13184 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13184 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13184 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13184 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13182 128 * √(2 / (13184 : ℝ)) *
      (√(13184 : ℝ) + paperT0 13184 + paperTail256 13184) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13184 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13184 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13184 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13182 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13182 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13184 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13184

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13184
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13184 (61 / 100) 166 (17 / (100 * 13184)) (26 / (10 * 13184)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13184 (61 / 100) 166 (17 / (100 * 13184)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (212982601 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1292370169 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (757679503 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13184 / 13184 * (61 / 100)) ^ 4 * inverseRadius8 (13184 - 1) /
            envelopeGap 13184 (61 / 100) 166 (17 / (100 * 13184)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13184

namespace BstLean.Part266.Row13184
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13184 166 ≤ (4173597337 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13184 166 ≤ (139238257 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (334659661 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13184 166 ≤ (1638614343 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13184 166 ≤ (29146069 / 2500000000000000000)
  w2 : (tableEnvelope C).w2 13184 166 ≤ (53246109 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (212982601 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (212982601 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1292370169 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (757679503 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3590879 / 1000000000) : ℝ) ≤ √(17 / (100 * 13184) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13184) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (515973111 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (35949550331 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13184) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13184) ≤ (107267413 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13184) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13184 * (166 : ℝ) ^ 2 + 26 / (10 * 13184) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13184) : ℝ)) (tA 13184 * 166 ^ 2 + 26 / (10 * 13184)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3590879 / 1000000000))) * ((212982601 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3590879 / 1000000000)) ^ 3) * ((1292370169 / 1000000000000000000000000))) + ((757679503 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3590879 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13184) : ℝ)) d.D d.V d.P (√(tA 13184) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3590879 / 1000000000)) ^ 2 * (((515973111 / 250000000000000)) * ((35949550331 / 1000000000000000000)))) + ((757679503 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13184) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3590879 / 1000000000)) * ((212982601 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13184) : ℝ)) (tA 13184 * 166 ^ 2 + 26 / (10 * 13184)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((212982601 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3590879 / 1000000000)) ^ 2) * ((1292370169 / 1000000000000000000000000)) + ((757679503 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13184) : ℝ)) (√(26 / (10 * 13184) : ℝ)) d.D d.V d.P (√(tA 13184) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3590879 / 1000000000)) * (((515973111 / 250000000000000)) * ((35949550331 / 1000000000000000000))) + ((757679503 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13184) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((212982601 / 50000000000000000000) : ℝ) + ((757679503 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13184

namespace BstLean.Part266.Row13184
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13184 166 ∧
    0 ≤ (tableEnvelope C).f1 13184 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13184 166 ∧
    0 ≤ (tableEnvelope C).w1 13184 166 ∧ 0 ≤ (tableEnvelope C).w2 13184 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13184 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13184 166 ∧ 0 ≤ d.f1 13184 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13184 166 ∧ 0 ≤ d.w1 13184 166 ∧ 0 ≤ d.w2 13184 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13184 ≤ 2 * (228 / 100 : ℝ) / 13184 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13184 ≤ 2 * (370 / 100 : ℝ) / 13184 := by
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
    (completeRAData (tableEnvelope C) 13184 166).locationBound 13184 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13184 166).energyBound 13184 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13184 166) (d.f1 13184 166) d.f2 ≤
      32 * (((4173597337 / 1000000000000000000) : ℝ) + (139238257 / 100000000000000000) + (334659661 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13184 166) (d.w1 13184 166)
      (d.w2 13184 166) ≤
      32 * (((1638614343 / 100000000000000000000) : ℝ) + (29146069 / 2500000000000000000) + (53246109 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13184 166) (d.f1 13184 166) d.f2 ≤
      ((4173597337 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4173597337 / 1000000000000000000)) * ((139238257 / 100000000000000000)) * (126 / 100) +
      2 * (((139238257 / 100000000000000000)) ^ 2 + 2 * ((4173597337 / 1000000000000000000)) * ((334659661 / 1000000000000000000))) +
      6 * ((139238257 / 100000000000000000)) * ((334659661 / 1000000000000000000)) * (126 / 100) + 8 * ((334659661 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13184 166) (d.f1 13184 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13184 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13184 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13184 166) (d.f1 13184 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13184 166) (d.w1 13184 166) (d.w2 13184 166)
  have hwexpr0 : 0 ≤ d.w0 13184 166 + d.w1 13184 166 * √(π / 2) +
      2 * d.w2 13184 166 + energyR16 13184 *
      radiusPolynomialRoot16 (d.w0 13184 166) (d.w1 13184 166) (d.w2 13184 166) := by
    positivity
  constructor
  · change (13184 : ℝ) ^ 8 * (mA 13184 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13184 166) (d.f1 13184 166) d.f2 + locationR16 13184 *
        radiusPolynomialRoot16 (d.f0 13184 166) (d.f1 13184 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13184 : ℝ) ^ 8 * (mA 13184 : ℝ) ^ 8 *
        ((((4173597337 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4173597337 / 1000000000000000000)) * ((139238257 / 100000000000000000)) * (126 / 100) +
          2 * (((139238257 / 100000000000000000)) ^ 2 + 2 * ((4173597337 / 1000000000000000000)) * ((334659661 / 1000000000000000000))) +
          6 * ((139238257 / 100000000000000000)) * ((334659661 / 1000000000000000000)) * (126 / 100) + 8 * ((334659661 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13184) *
          (32 * (((4173597337 / 1000000000000000000) : ℝ) + (139238257 / 100000000000000000) + (334659661 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13184 : ℝ) ^ 16 *
      (d.w0 13184 166 + d.w1 13184 166 * √(π / 2) + 2 * d.w2 13184 166 +
        energyR16 13184 * radiusPolynomialRoot16 (d.w0 13184 166) (d.w1 13184 166)
          (d.w2 13184 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13184 : ℝ) ^ 16 *
        (((1638614343 / 100000000000000000000) : ℝ) + ((29146069 / 2500000000000000000)) * (126 / 100) + 2 * ((53246109 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13184) *
          (32 * (((1638614343 / 100000000000000000000) : ℝ) + (29146069 / 2500000000000000000) + (53246109 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13184

/-! A coarse bound on the actual paper statistics constant at dimension 13185. -/
namespace BstLean.Part266.Row13185
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13183 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13183 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13183 128 ≤ (13437 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13437 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13185) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13185 : ℕ))
    (by norm_num : (13185 : ℕ) ≤ 16384)
  have ht : paperTail256 13185 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13185 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13185 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13185 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13185 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13185 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13183 128 * √(2 / (13185 : ℝ)) *
      (√(13185 : ℝ) + paperT0 13185 + paperTail256 13185) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13185 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13185 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13185 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13183 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13183 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13185 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13185

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13185
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13185 (61 / 100) 166 (17 / (100 * 13185)) (26 / (10 * 13185)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13185 (61 / 100) 166 (17 / (100 * 13185)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (106467071 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (645989063 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3786077983 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13185 / 13185 * (61 / 100)) ^ 4 * inverseRadius8 (13185 - 1) /
            envelopeGap 13185 (61 / 100) 166 (17 / (100 * 13185)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13185

namespace BstLean.Part266.Row13185
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13185 166 ≤ (260800337 / 62500000000000000)
  f1 : (tableEnvelope C).f1 13185 166 ≤ (174014803 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (33459619 / 100000000000000000)
  w0 : (tableEnvelope C).w0 13185 166 ≤ (1638241397 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13185 166 ≤ (291394361 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 13185 166 ≤ (26616997 / 6250000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (106467071 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (106467071 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (645989063 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3786077983 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3590743 / 1000000000) : ℝ) ≤ √(17 / (100 * 13185) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13185) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2063657637 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7188819447 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13185) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13185) ≤ (107259277 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13185) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13185 * (166 : ℝ) ^ 2 + 26 / (10 * 13185) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13185) : ℝ)) (tA 13185 * 166 ^ 2 + 26 / (10 * 13185)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3590743 / 1000000000))) * ((106467071 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3590743 / 1000000000)) ^ 3) * ((645989063 / 500000000000000000000000))) + ((3786077983 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3590743 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13185) : ℝ)) d.D d.V d.P (√(tA 13185) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3590743 / 1000000000)) ^ 2 * (((2063657637 / 1000000000000000)) * ((7188819447 / 200000000000000000)))) + ((3786077983 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13185) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3590743 / 1000000000)) * ((106467071 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13185) : ℝ)) (tA 13185 * 166 ^ 2 + 26 / (10 * 13185)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((106467071 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3590743 / 1000000000)) ^ 2) * ((645989063 / 500000000000000000000000)) + ((3786077983 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13185) : ℝ)) (√(26 / (10 * 13185) : ℝ)) d.D d.V d.P (√(tA 13185) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3590743 / 1000000000)) * (((2063657637 / 1000000000000000)) * ((7188819447 / 200000000000000000))) + ((3786077983 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13185) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((106467071 / 25000000000000000000) : ℝ) + ((3786077983 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13185

namespace BstLean.Part266.Row13185
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13185 166 ∧
    0 ≤ (tableEnvelope C).f1 13185 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13185 166 ∧
    0 ≤ (tableEnvelope C).w1 13185 166 ∧ 0 ≤ (tableEnvelope C).w2 13185 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13185 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13185 166 ∧ 0 ≤ d.f1 13185 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13185 166 ∧ 0 ≤ d.w1 13185 166 ∧ 0 ≤ d.w2 13185 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13185 ≤ 2 * (228 / 100 : ℝ) / 13185 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13185 ≤ 2 * (370 / 100 : ℝ) / 13185 := by
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
    (completeRAData (tableEnvelope C) 13185 166).locationBound 13185 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13185 166).energyBound 13185 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13185 166) (d.f1 13185 166) d.f2 ≤
      32 * (((260800337 / 62500000000000000) : ℝ) + (174014803 / 125000000000000000) + (33459619 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13185 166) (d.w1 13185 166)
      (d.w2 13185 166) ≤
      32 * (((1638241397 / 100000000000000000000) : ℝ) + (291394361 / 25000000000000000000) + (26616997 / 6250000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13185 166) (d.f1 13185 166) d.f2 ≤
      ((260800337 / 62500000000000000) : ℝ) ^ 2 + 2 * ((260800337 / 62500000000000000)) * ((174014803 / 125000000000000000)) * (126 / 100) +
      2 * (((174014803 / 125000000000000000)) ^ 2 + 2 * ((260800337 / 62500000000000000)) * ((33459619 / 100000000000000000))) +
      6 * ((174014803 / 125000000000000000)) * ((33459619 / 100000000000000000)) * (126 / 100) + 8 * ((33459619 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13185 166) (d.f1 13185 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13185 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13185 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13185 166) (d.f1 13185 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13185 166) (d.w1 13185 166) (d.w2 13185 166)
  have hwexpr0 : 0 ≤ d.w0 13185 166 + d.w1 13185 166 * √(π / 2) +
      2 * d.w2 13185 166 + energyR16 13185 *
      radiusPolynomialRoot16 (d.w0 13185 166) (d.w1 13185 166) (d.w2 13185 166) := by
    positivity
  constructor
  · change (13185 : ℝ) ^ 8 * (mA 13185 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13185 166) (d.f1 13185 166) d.f2 + locationR16 13185 *
        radiusPolynomialRoot16 (d.f0 13185 166) (d.f1 13185 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13185 : ℝ) ^ 8 * (mA 13185 : ℝ) ^ 8 *
        ((((260800337 / 62500000000000000) : ℝ) ^ 2 + 2 * ((260800337 / 62500000000000000)) * ((174014803 / 125000000000000000)) * (126 / 100) +
          2 * (((174014803 / 125000000000000000)) ^ 2 + 2 * ((260800337 / 62500000000000000)) * ((33459619 / 100000000000000000))) +
          6 * ((174014803 / 125000000000000000)) * ((33459619 / 100000000000000000)) * (126 / 100) + 8 * ((33459619 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13185) *
          (32 * (((260800337 / 62500000000000000) : ℝ) + (174014803 / 125000000000000000) + (33459619 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13185 : ℝ) ^ 16 *
      (d.w0 13185 166 + d.w1 13185 166 * √(π / 2) + 2 * d.w2 13185 166 +
        energyR16 13185 * radiusPolynomialRoot16 (d.w0 13185 166) (d.w1 13185 166)
          (d.w2 13185 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13185 : ℝ) ^ 16 *
        (((1638241397 / 100000000000000000000) : ℝ) + ((291394361 / 25000000000000000000)) * (126 / 100) + 2 * ((26616997 / 6250000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13185) *
          (32 * (((1638241397 / 100000000000000000000) : ℝ) + (291394361 / 25000000000000000000) + (26616997 / 6250000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13185

/-! A coarse bound on the actual paper statistics constant at dimension 13186. -/
namespace BstLean.Part266.Row13186
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13184 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13184 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13184 128 ≤ (13438 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13438 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13186) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13186 : ℕ))
    (by norm_num : (13186 : ℕ) ≤ 16384)
  have ht : paperTail256 13186 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13186 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13186 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13186 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13186 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13186 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13184 128 * √(2 / (13186 : ℝ)) *
      (√(13186 : ℝ) + paperT0 13186 + paperTail256 13186) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13186 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13186 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13186 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13184 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13184 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13186 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13186

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13186
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13186 (61 / 100) 166 (17 / (100 * 13186)) (26 / (10 * 13186)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13186 (61 / 100) 166 (17 / (100 * 13186)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (106442849 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1291586231 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3783760051 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13186 / 13186 * (61 / 100)) ^ 4 * inverseRadius8 (13186 - 1) /
            envelopeGap 13186 (61 / 100) 166 (17 / (100 * 13186)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13186

namespace BstLean.Part266.Row13186
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13186 166 ≤ (1043003427 / 250000000000000000)
  f1 : (tableEnvelope C).f1 13186 166 ≤ (1391854361 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (334532737 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13186 166 ≤ (51183393 / 3125000000000000000)
  w1 : (tableEnvelope C).w1 13186 166 ≤ (582656107 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13186 166 ≤ (212887531 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (106442849 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (106442849 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1291586231 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3783760051 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3590607 / 1000000000) : ℝ) ≤ √(17 / (100 * 13186) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13186) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (16507383 / 8000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3593864537 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13186) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13186) ≤ (107251143 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13186) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13186 * (166 : ℝ) ^ 2 + 26 / (10 * 13186) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13186) : ℝ)) (tA 13186 * 166 ^ 2 + 26 / (10 * 13186)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3590607 / 1000000000))) * ((106442849 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3590607 / 1000000000)) ^ 3) * ((1291586231 / 1000000000000000000000000))) + ((3783760051 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3590607 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13186) : ℝ)) d.D d.V d.P (√(tA 13186) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3590607 / 1000000000)) ^ 2 * (((16507383 / 8000000000000)) * ((3593864537 / 100000000000000000)))) + ((3783760051 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13186) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3590607 / 1000000000)) * ((106442849 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13186) : ℝ)) (tA 13186 * 166 ^ 2 + 26 / (10 * 13186)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((106442849 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3590607 / 1000000000)) ^ 2) * ((1291586231 / 1000000000000000000000000)) + ((3783760051 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13186) : ℝ)) (√(26 / (10 * 13186) : ℝ)) d.D d.V d.P (√(tA 13186) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3590607 / 1000000000)) * (((16507383 / 8000000000000)) * ((3593864537 / 100000000000000000))) + ((3783760051 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13186) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((106442849 / 25000000000000000000) : ℝ) + ((3783760051 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13186

namespace BstLean.Part266.Row13186
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13186 166 ∧
    0 ≤ (tableEnvelope C).f1 13186 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13186 166 ∧
    0 ≤ (tableEnvelope C).w1 13186 166 ∧ 0 ≤ (tableEnvelope C).w2 13186 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13186 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13186 166 ∧ 0 ≤ d.f1 13186 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13186 166 ∧ 0 ≤ d.w1 13186 166 ∧ 0 ≤ d.w2 13186 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13186 ≤ 2 * (228 / 100 : ℝ) / 13186 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13186 ≤ 2 * (370 / 100 : ℝ) / 13186 := by
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
    (completeRAData (tableEnvelope C) 13186 166).locationBound 13186 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13186 166).energyBound 13186 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13186 166) (d.f1 13186 166) d.f2 ≤
      32 * (((1043003427 / 250000000000000000) : ℝ) + (1391854361 / 1000000000000000000) + (334532737 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13186 166) (d.w1 13186 166)
      (d.w2 13186 166) ≤
      32 * (((51183393 / 3125000000000000000) : ℝ) + (582656107 / 50000000000000000000) + (212887531 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13186 166) (d.f1 13186 166) d.f2 ≤
      ((1043003427 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1043003427 / 250000000000000000)) * ((1391854361 / 1000000000000000000)) * (126 / 100) +
      2 * (((1391854361 / 1000000000000000000)) ^ 2 + 2 * ((1043003427 / 250000000000000000)) * ((334532737 / 1000000000000000000))) +
      6 * ((1391854361 / 1000000000000000000)) * ((334532737 / 1000000000000000000)) * (126 / 100) + 8 * ((334532737 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13186 166) (d.f1 13186 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13186 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13186 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13186 166) (d.f1 13186 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13186 166) (d.w1 13186 166) (d.w2 13186 166)
  have hwexpr0 : 0 ≤ d.w0 13186 166 + d.w1 13186 166 * √(π / 2) +
      2 * d.w2 13186 166 + energyR16 13186 *
      radiusPolynomialRoot16 (d.w0 13186 166) (d.w1 13186 166) (d.w2 13186 166) := by
    positivity
  constructor
  · change (13186 : ℝ) ^ 8 * (mA 13186 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13186 166) (d.f1 13186 166) d.f2 + locationR16 13186 *
        radiusPolynomialRoot16 (d.f0 13186 166) (d.f1 13186 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13186 : ℝ) ^ 8 * (mA 13186 : ℝ) ^ 8 *
        ((((1043003427 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1043003427 / 250000000000000000)) * ((1391854361 / 1000000000000000000)) * (126 / 100) +
          2 * (((1391854361 / 1000000000000000000)) ^ 2 + 2 * ((1043003427 / 250000000000000000)) * ((334532737 / 1000000000000000000))) +
          6 * ((1391854361 / 1000000000000000000)) * ((334532737 / 1000000000000000000)) * (126 / 100) + 8 * ((334532737 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13186) *
          (32 * (((1043003427 / 250000000000000000) : ℝ) + (1391854361 / 1000000000000000000) + (334532737 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13186 : ℝ) ^ 16 *
      (d.w0 13186 166 + d.w1 13186 166 * √(π / 2) + 2 * d.w2 13186 166 +
        energyR16 13186 * radiusPolynomialRoot16 (d.w0 13186 166) (d.w1 13186 166)
          (d.w2 13186 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13186 : ℝ) ^ 16 *
        (((51183393 / 3125000000000000000) : ℝ) + ((582656107 / 50000000000000000000)) * (126 / 100) + 2 * ((212887531 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13186) *
          (32 * (((51183393 / 3125000000000000000) : ℝ) + (582656107 / 50000000000000000000) + (212887531 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13186

/-! A coarse bound on the actual paper statistics constant at dimension 13187. -/
namespace BstLean.Part266.Row13187
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13185 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13185 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13185 128 ≤ (13439 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13439 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13187) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13187 : ℕ))
    (by norm_num : (13187 : ℕ) ≤ 16384)
  have ht : paperTail256 13187 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13187 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13187 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13187 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13187 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13187 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13185 128 * √(2 / (13187 : ℝ)) *
      (√(13187 : ℝ) + paperT0 13187 + paperTail256 13187) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13187 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13187 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13187 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13185 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13185 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13187 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13187

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13187
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13187 (61 / 100) 166 (17 / (100 * 13187)) (26 / (10 * 13187)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13187 (61 / 100) 166 (17 / (100 * 13187)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (53209317 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (258238897 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3781443717 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13187 / 13187 * (61 / 100)) ^ 4 * inverseRadius8 (13187 - 1) /
            envelopeGap 13187 (61 / 100) 166 (17 / (100 * 13187)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13187

namespace BstLean.Part266.Row13187
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13187 166 ≤ (4171222287 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13187 166 ≤ (695795189 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (167234651 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13187 166 ≤ (409373969 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 13187 166 ≤ (291261767 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 13187 166 ≤ (2128391 / 500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (53209317 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (53209317 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (258238897 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3781443717 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3590471 / 1000000000) : ℝ) ≤ √(17 / (100 * 13187) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13187) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (412637631 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (35933194751 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13187) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13187) ≤ (10724301 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13187) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13187 * (166 : ℝ) ^ 2 + 26 / (10 * 13187) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13187) : ℝ)) (tA 13187 * 166 ^ 2 + 26 / (10 * 13187)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3590471 / 1000000000))) * ((53209317 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3590471 / 1000000000)) ^ 3) * ((258238897 / 200000000000000000000000))) + ((3781443717 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3590471 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13187) : ℝ)) d.D d.V d.P (√(tA 13187) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3590471 / 1000000000)) ^ 2 * (((412637631 / 200000000000000)) * ((35933194751 / 1000000000000000000)))) + ((3781443717 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13187) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3590471 / 1000000000)) * ((53209317 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13187) : ℝ)) (tA 13187 * 166 ^ 2 + 26 / (10 * 13187)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((53209317 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3590471 / 1000000000)) ^ 2) * ((258238897 / 200000000000000000000000)) + ((3781443717 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13187) : ℝ)) (√(26 / (10 * 13187) : ℝ)) d.D d.V d.P (√(tA 13187) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3590471 / 1000000000)) * (((412637631 / 200000000000000)) * ((35933194751 / 1000000000000000000))) + ((3781443717 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13187) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((53209317 / 12500000000000000000) : ℝ) + ((3781443717 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13187

namespace BstLean.Part266.Row13187
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13187 166 ∧
    0 ≤ (tableEnvelope C).f1 13187 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13187 166 ∧
    0 ≤ (tableEnvelope C).w1 13187 166 ∧ 0 ≤ (tableEnvelope C).w2 13187 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13187 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13187 166 ∧ 0 ≤ d.f1 13187 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13187 166 ∧ 0 ≤ d.w1 13187 166 ∧ 0 ≤ d.w2 13187 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13187 ≤ 2 * (228 / 100 : ℝ) / 13187 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13187 ≤ 2 * (370 / 100 : ℝ) / 13187 := by
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
    (completeRAData (tableEnvelope C) 13187 166).locationBound 13187 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13187 166).energyBound 13187 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13187 166) (d.f1 13187 166) d.f2 ≤
      32 * (((4171222287 / 1000000000000000000) : ℝ) + (695795189 / 500000000000000000) + (167234651 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13187 166) (d.w1 13187 166)
      (d.w2 13187 166) ≤
      32 * (((409373969 / 25000000000000000000) : ℝ) + (291261767 / 25000000000000000000) + (2128391 / 500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13187 166) (d.f1 13187 166) d.f2 ≤
      ((4171222287 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4171222287 / 1000000000000000000)) * ((695795189 / 500000000000000000)) * (126 / 100) +
      2 * (((695795189 / 500000000000000000)) ^ 2 + 2 * ((4171222287 / 1000000000000000000)) * ((167234651 / 500000000000000000))) +
      6 * ((695795189 / 500000000000000000)) * ((167234651 / 500000000000000000)) * (126 / 100) + 8 * ((167234651 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13187 166) (d.f1 13187 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13187 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13187 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13187 166) (d.f1 13187 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13187 166) (d.w1 13187 166) (d.w2 13187 166)
  have hwexpr0 : 0 ≤ d.w0 13187 166 + d.w1 13187 166 * √(π / 2) +
      2 * d.w2 13187 166 + energyR16 13187 *
      radiusPolynomialRoot16 (d.w0 13187 166) (d.w1 13187 166) (d.w2 13187 166) := by
    positivity
  constructor
  · change (13187 : ℝ) ^ 8 * (mA 13187 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13187 166) (d.f1 13187 166) d.f2 + locationR16 13187 *
        radiusPolynomialRoot16 (d.f0 13187 166) (d.f1 13187 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13187 : ℝ) ^ 8 * (mA 13187 : ℝ) ^ 8 *
        ((((4171222287 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4171222287 / 1000000000000000000)) * ((695795189 / 500000000000000000)) * (126 / 100) +
          2 * (((695795189 / 500000000000000000)) ^ 2 + 2 * ((4171222287 / 1000000000000000000)) * ((167234651 / 500000000000000000))) +
          6 * ((695795189 / 500000000000000000)) * ((167234651 / 500000000000000000)) * (126 / 100) + 8 * ((167234651 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13187) *
          (32 * (((4171222287 / 1000000000000000000) : ℝ) + (695795189 / 500000000000000000) + (167234651 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13187 : ℝ) ^ 16 *
      (d.w0 13187 166 + d.w1 13187 166 * √(π / 2) + 2 * d.w2 13187 166 +
        energyR16 13187 * radiusPolynomialRoot16 (d.w0 13187 166) (d.w1 13187 166)
          (d.w2 13187 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13187 : ℝ) ^ 16 *
        (((409373969 / 25000000000000000000) : ℝ) + ((291261767 / 25000000000000000000)) * (126 / 100) + 2 * ((2128391 / 500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13187) *
          (32 * (((409373969 / 25000000000000000000) : ℝ) + (291261767 / 25000000000000000000) + (2128391 / 500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13187

/-! A coarse bound on the actual paper statistics constant at dimension 13188. -/
namespace BstLean.Part266.Row13188
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13186 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13186 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13186 128 ≤ (13440 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13440 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13188) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13188 : ℕ))
    (by norm_num : (13188 : ℕ) ≤ 16384)
  have ht : paperTail256 13188 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13188 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13188 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13188 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13188 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13188 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13186 128 * √(2 / (13188 : ℝ)) *
      (√(13188 : ℝ) + paperT0 13188 + paperTail256 13188) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13188 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13188 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13188 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13186 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13186 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13188 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13188

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13188
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13188 (61 / 100) 166 (17 / (100 * 13188)) (26 / (10 * 13188)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13188 (61 / 100) 166 (17 / (100 * 13188)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (425577707 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (161350361 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3779128979 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13188 / 13188 * (61 / 100)) ^ 4 * inverseRadius8 (13188 - 1) /
            envelopeGap 13188 (61 / 100) 166 (17 / (100 * 13188)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13188

namespace BstLean.Part266.Row13188
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13188 166 ≤ (417043113 / 100000000000000000)
  f1 : (tableEnvelope C).f1 13188 166 ≤ (1391326479 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (167202943 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13188 166 ≤ (1637123303 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13188 166 ≤ (1164782009 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13188 166 ≤ (53197671 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (425577707 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (425577707 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (161350361 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3779128979 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((718067 / 200000000) : ℝ) ≤ √(17 / (100 * 13188) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13188) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2062953483 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (35927745379 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13188) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13188) ≤ (53617439 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13188) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13188 * (166 : ℝ) ^ 2 + 26 / (10 * 13188) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13188) : ℝ)) (tA 13188 * 166 ^ 2 + 26 / (10 * 13188)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((718067 / 200000000))) * ((425577707 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((718067 / 200000000)) ^ 3) * ((161350361 / 125000000000000000000000))) + ((3779128979 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((718067 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13188) : ℝ)) d.D d.V d.P (√(tA 13188) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((718067 / 200000000)) ^ 2 * (((2062953483 / 1000000000000000)) * ((35927745379 / 1000000000000000000)))) + ((3779128979 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13188) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((718067 / 200000000)) * ((425577707 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13188) : ℝ)) (tA 13188 * 166 ^ 2 + 26 / (10 * 13188)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((425577707 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((718067 / 200000000)) ^ 2) * ((161350361 / 125000000000000000000000)) + ((3779128979 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13188) : ℝ)) (√(26 / (10 * 13188) : ℝ)) d.D d.V d.P (√(tA 13188) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((718067 / 200000000)) * (((2062953483 / 1000000000000000)) * ((35927745379 / 1000000000000000000))) + ((3779128979 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13188) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((425577707 / 100000000000000000000) : ℝ) + ((3779128979 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13188

namespace BstLean.Part266.Row13188
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13188 166 ∧
    0 ≤ (tableEnvelope C).f1 13188 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13188 166 ∧
    0 ≤ (tableEnvelope C).w1 13188 166 ∧ 0 ≤ (tableEnvelope C).w2 13188 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13188 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13188 166 ∧ 0 ≤ d.f1 13188 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13188 166 ∧ 0 ≤ d.w1 13188 166 ∧ 0 ≤ d.w2 13188 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13188 ≤ 2 * (228 / 100 : ℝ) / 13188 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13188 ≤ 2 * (370 / 100 : ℝ) / 13188 := by
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
    (completeRAData (tableEnvelope C) 13188 166).locationBound 13188 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13188 166).energyBound 13188 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13188 166) (d.f1 13188 166) d.f2 ≤
      32 * (((417043113 / 100000000000000000) : ℝ) + (1391326479 / 1000000000000000000) + (167202943 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13188 166) (d.w1 13188 166)
      (d.w2 13188 166) ≤
      32 * (((1637123303 / 100000000000000000000) : ℝ) + (1164782009 / 100000000000000000000) + (53197671 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13188 166) (d.f1 13188 166) d.f2 ≤
      ((417043113 / 100000000000000000) : ℝ) ^ 2 + 2 * ((417043113 / 100000000000000000)) * ((1391326479 / 1000000000000000000)) * (126 / 100) +
      2 * (((1391326479 / 1000000000000000000)) ^ 2 + 2 * ((417043113 / 100000000000000000)) * ((167202943 / 500000000000000000))) +
      6 * ((1391326479 / 1000000000000000000)) * ((167202943 / 500000000000000000)) * (126 / 100) + 8 * ((167202943 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13188 166) (d.f1 13188 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13188 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13188 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13188 166) (d.f1 13188 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13188 166) (d.w1 13188 166) (d.w2 13188 166)
  have hwexpr0 : 0 ≤ d.w0 13188 166 + d.w1 13188 166 * √(π / 2) +
      2 * d.w2 13188 166 + energyR16 13188 *
      radiusPolynomialRoot16 (d.w0 13188 166) (d.w1 13188 166) (d.w2 13188 166) := by
    positivity
  constructor
  · change (13188 : ℝ) ^ 8 * (mA 13188 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13188 166) (d.f1 13188 166) d.f2 + locationR16 13188 *
        radiusPolynomialRoot16 (d.f0 13188 166) (d.f1 13188 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13188 : ℝ) ^ 8 * (mA 13188 : ℝ) ^ 8 *
        ((((417043113 / 100000000000000000) : ℝ) ^ 2 + 2 * ((417043113 / 100000000000000000)) * ((1391326479 / 1000000000000000000)) * (126 / 100) +
          2 * (((1391326479 / 1000000000000000000)) ^ 2 + 2 * ((417043113 / 100000000000000000)) * ((167202943 / 500000000000000000))) +
          6 * ((1391326479 / 1000000000000000000)) * ((167202943 / 500000000000000000)) * (126 / 100) + 8 * ((167202943 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13188) *
          (32 * (((417043113 / 100000000000000000) : ℝ) + (1391326479 / 1000000000000000000) + (167202943 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13188 : ℝ) ^ 16 *
      (d.w0 13188 166 + d.w1 13188 166 * √(π / 2) + 2 * d.w2 13188 166 +
        energyR16 13188 * radiusPolynomialRoot16 (d.w0 13188 166) (d.w1 13188 166)
          (d.w2 13188 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13188 : ℝ) ^ 16 *
        (((1637123303 / 100000000000000000000) : ℝ) + ((1164782009 / 100000000000000000000)) * (126 / 100) + 2 * ((53197671 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13188) *
          (32 * (((1637123303 / 100000000000000000000) : ℝ) + (1164782009 / 100000000000000000000) + (53197671 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13188

/-! A coarse bound on the actual paper statistics constant at dimension 13189. -/
namespace BstLean.Part266.Row13189
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13187 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13187 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13187 128 ≤ (13441 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13441 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13189) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13189 : ℕ))
    (by norm_num : (13189 : ℕ) ≤ 16384)
  have ht : paperTail256 13189 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13189 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13189 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13189 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13189 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13189 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13187 128 * √(2 / (13189 : ℝ)) *
      (√(13189 : ℝ) + paperT0 13189 + paperTail256 13189) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13189 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13189 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13189 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13187 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13187 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13189 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13189

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13189
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13189 (61 / 100) 166 (17 / (100 * 13189)) (26 / (10 * 13189)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13189 (61 / 100) 166 (17 / (100 * 13189)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (212740453 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1290411439 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3776815837 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13189 / 13189 * (61 / 100)) ^ 4 * inverseRadius8 (13189 - 1) /
            envelopeGap 13189 (61 / 100) 166 (17 / (100 * 13189)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13189

namespace BstLean.Part266.Row13189
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13189 166 ≤ (521205029 / 125000000000000000)
  f1 : (tableEnvelope C).f1 13189 166 ≤ (1391062661 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (41792811 / 125000000000000000)
  w0 : (tableEnvelope C).w0 13189 166 ≤ (1636750851 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13189 166 ≤ (582258517 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13189 166 ≤ (85096913 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (212740453 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (212740453 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1290411439 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3776815837 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3590199 / 1000000000) : ℝ) ≤ √(17 / (100 * 13189) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13189) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (515679713 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (35922297241 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13189) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13189) ≤ (107226747 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13189) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13189 * (166 : ℝ) ^ 2 + 26 / (10 * 13189) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13189) : ℝ)) (tA 13189 * 166 ^ 2 + 26 / (10 * 13189)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3590199 / 1000000000))) * ((212740453 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3590199 / 1000000000)) ^ 3) * ((1290411439 / 1000000000000000000000000))) + ((3776815837 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3590199 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13189) : ℝ)) d.D d.V d.P (√(tA 13189) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3590199 / 1000000000)) ^ 2 * (((515679713 / 250000000000000)) * ((35922297241 / 1000000000000000000)))) + ((3776815837 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13189) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3590199 / 1000000000)) * ((212740453 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13189) : ℝ)) (tA 13189 * 166 ^ 2 + 26 / (10 * 13189)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((212740453 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3590199 / 1000000000)) ^ 2) * ((1290411439 / 1000000000000000000000000)) + ((3776815837 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13189) : ℝ)) (√(26 / (10 * 13189) : ℝ)) d.D d.V d.P (√(tA 13189) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3590199 / 1000000000)) * (((515679713 / 250000000000000)) * ((35922297241 / 1000000000000000000))) + ((3776815837 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13189) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((212740453 / 50000000000000000000) : ℝ) + ((3776815837 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13189

namespace BstLean.Part266.Row13189
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13189 166 ∧
    0 ≤ (tableEnvelope C).f1 13189 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13189 166 ∧
    0 ≤ (tableEnvelope C).w1 13189 166 ∧ 0 ≤ (tableEnvelope C).w2 13189 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13189 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13189 166 ∧ 0 ≤ d.f1 13189 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13189 166 ∧ 0 ≤ d.w1 13189 166 ∧ 0 ≤ d.w2 13189 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13189 ≤ 2 * (228 / 100 : ℝ) / 13189 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13189 ≤ 2 * (370 / 100 : ℝ) / 13189 := by
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
    (completeRAData (tableEnvelope C) 13189 166).locationBound 13189 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13189 166).energyBound 13189 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13189 166) (d.f1 13189 166) d.f2 ≤
      32 * (((521205029 / 125000000000000000) : ℝ) + (1391062661 / 1000000000000000000) + (41792811 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13189 166) (d.w1 13189 166)
      (d.w2 13189 166) ≤
      32 * (((1636750851 / 100000000000000000000) : ℝ) + (582258517 / 50000000000000000000) + (85096913 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13189 166) (d.f1 13189 166) d.f2 ≤
      ((521205029 / 125000000000000000) : ℝ) ^ 2 + 2 * ((521205029 / 125000000000000000)) * ((1391062661 / 1000000000000000000)) * (126 / 100) +
      2 * (((1391062661 / 1000000000000000000)) ^ 2 + 2 * ((521205029 / 125000000000000000)) * ((41792811 / 125000000000000000))) +
      6 * ((1391062661 / 1000000000000000000)) * ((41792811 / 125000000000000000)) * (126 / 100) + 8 * ((41792811 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13189 166) (d.f1 13189 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13189 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13189 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13189 166) (d.f1 13189 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13189 166) (d.w1 13189 166) (d.w2 13189 166)
  have hwexpr0 : 0 ≤ d.w0 13189 166 + d.w1 13189 166 * √(π / 2) +
      2 * d.w2 13189 166 + energyR16 13189 *
      radiusPolynomialRoot16 (d.w0 13189 166) (d.w1 13189 166) (d.w2 13189 166) := by
    positivity
  constructor
  · change (13189 : ℝ) ^ 8 * (mA 13189 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13189 166) (d.f1 13189 166) d.f2 + locationR16 13189 *
        radiusPolynomialRoot16 (d.f0 13189 166) (d.f1 13189 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13189 : ℝ) ^ 8 * (mA 13189 : ℝ) ^ 8 *
        ((((521205029 / 125000000000000000) : ℝ) ^ 2 + 2 * ((521205029 / 125000000000000000)) * ((1391062661 / 1000000000000000000)) * (126 / 100) +
          2 * (((1391062661 / 1000000000000000000)) ^ 2 + 2 * ((521205029 / 125000000000000000)) * ((41792811 / 125000000000000000))) +
          6 * ((1391062661 / 1000000000000000000)) * ((41792811 / 125000000000000000)) * (126 / 100) + 8 * ((41792811 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13189) *
          (32 * (((521205029 / 125000000000000000) : ℝ) + (1391062661 / 1000000000000000000) + (41792811 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13189 : ℝ) ^ 16 *
      (d.w0 13189 166 + d.w1 13189 166 * √(π / 2) + 2 * d.w2 13189 166 +
        energyR16 13189 * radiusPolynomialRoot16 (d.w0 13189 166) (d.w1 13189 166)
          (d.w2 13189 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13189 : ℝ) ^ 16 *
        (((1636750851 / 100000000000000000000) : ℝ) + ((582258517 / 50000000000000000000)) * (126 / 100) + 2 * ((85096913 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13189) *
          (32 * (((1636750851 / 100000000000000000000) : ℝ) + (582258517 / 50000000000000000000) + (85096913 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13189

/-! A coarse bound on the actual paper statistics constant at dimension 13190. -/
namespace BstLean.Part266.Row13190
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13188 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13188 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13188 128 ≤ (13442 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13442 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13190) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13190 : ℕ))
    (by norm_num : (13190 : ℕ) ≤ 16384)
  have ht : paperTail256 13190 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13190 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13190 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13190 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13190 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13190 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13188 128 * √(2 / (13190 : ℝ)) *
      (√(13190 : ℝ) + paperT0 13190 + paperTail256 13190) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13190 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13190 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13190 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13188 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13188 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13190 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13190

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13190
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13190 (61 / 100) 166 (17 / (100 * 13190)) (26 / (10 * 13190)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13190 (61 / 100) 166 (17 / (100 * 13190)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (85076827 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1290020139 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3774504289 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13190 / 13190 * (61 / 100)) ^ 4 * inverseRadius8 (13190 - 1) /
            envelopeGap 13190 (61 / 100) 166 (17 / (100 * 13190)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13190

namespace BstLean.Part266.Row13190
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13190 166 ≤ (4168852951 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13190 166 ≤ (13907997 / 10000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (334279201 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13190 166 ≤ (818189599 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13190 166 ≤ (116425247 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 13190 166 ≤ (26586737 / 6250000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (85076827 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (85076827 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1290020139 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3774504289 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1795031 / 500000000) : ℝ) ≤ √(17 / (100 * 13190) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13190) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2062484267 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (718337007 / 20000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13190) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13190) ≤ (53609309 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13190) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13190 * (166 : ℝ) ^ 2 + 26 / (10 * 13190) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13190) : ℝ)) (tA 13190 * 166 ^ 2 + 26 / (10 * 13190)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1795031 / 500000000))) * ((85076827 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1795031 / 500000000)) ^ 3) * ((1290020139 / 1000000000000000000000000))) + ((3774504289 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1795031 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13190) : ℝ)) d.D d.V d.P (√(tA 13190) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1795031 / 500000000)) ^ 2 * (((2062484267 / 1000000000000000)) * ((718337007 / 20000000000000000)))) + ((3774504289 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13190) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1795031 / 500000000)) * ((85076827 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13190) : ℝ)) (tA 13190 * 166 ^ 2 + 26 / (10 * 13190)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((85076827 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1795031 / 500000000)) ^ 2) * ((1290020139 / 1000000000000000000000000)) + ((3774504289 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13190) : ℝ)) (√(26 / (10 * 13190) : ℝ)) d.D d.V d.P (√(tA 13190) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1795031 / 500000000)) * (((2062484267 / 1000000000000000)) * ((718337007 / 20000000000000000))) + ((3774504289 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13190) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((85076827 / 20000000000000000000) : ℝ) + ((3774504289 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13190

namespace BstLean.Part266.Row13190
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13190 166 ∧
    0 ≤ (tableEnvelope C).f1 13190 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13190 166 ∧
    0 ≤ (tableEnvelope C).w1 13190 166 ∧ 0 ≤ (tableEnvelope C).w2 13190 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13190 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13190 166 ∧ 0 ≤ d.f1 13190 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13190 166 ∧ 0 ≤ d.w1 13190 166 ∧ 0 ≤ d.w2 13190 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13190 ≤ 2 * (228 / 100 : ℝ) / 13190 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13190 ≤ 2 * (370 / 100 : ℝ) / 13190 := by
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
    (completeRAData (tableEnvelope C) 13190 166).locationBound 13190 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13190 166).energyBound 13190 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13190 166) (d.f1 13190 166) d.f2 ≤
      32 * (((4168852951 / 1000000000000000000) : ℝ) + (13907997 / 10000000000000000) + (334279201 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13190 166) (d.w1 13190 166)
      (d.w2 13190 166) ≤
      32 * (((818189599 / 50000000000000000000) : ℝ) + (116425247 / 10000000000000000000) + (26586737 / 6250000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13190 166) (d.f1 13190 166) d.f2 ≤
      ((4168852951 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4168852951 / 1000000000000000000)) * ((13907997 / 10000000000000000)) * (126 / 100) +
      2 * (((13907997 / 10000000000000000)) ^ 2 + 2 * ((4168852951 / 1000000000000000000)) * ((334279201 / 1000000000000000000))) +
      6 * ((13907997 / 10000000000000000)) * ((334279201 / 1000000000000000000)) * (126 / 100) + 8 * ((334279201 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13190 166) (d.f1 13190 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13190 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13190 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13190 166) (d.f1 13190 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13190 166) (d.w1 13190 166) (d.w2 13190 166)
  have hwexpr0 : 0 ≤ d.w0 13190 166 + d.w1 13190 166 * √(π / 2) +
      2 * d.w2 13190 166 + energyR16 13190 *
      radiusPolynomialRoot16 (d.w0 13190 166) (d.w1 13190 166) (d.w2 13190 166) := by
    positivity
  constructor
  · change (13190 : ℝ) ^ 8 * (mA 13190 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13190 166) (d.f1 13190 166) d.f2 + locationR16 13190 *
        radiusPolynomialRoot16 (d.f0 13190 166) (d.f1 13190 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13190 : ℝ) ^ 8 * (mA 13190 : ℝ) ^ 8 *
        ((((4168852951 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4168852951 / 1000000000000000000)) * ((13907997 / 10000000000000000)) * (126 / 100) +
          2 * (((13907997 / 10000000000000000)) ^ 2 + 2 * ((4168852951 / 1000000000000000000)) * ((334279201 / 1000000000000000000))) +
          6 * ((13907997 / 10000000000000000)) * ((334279201 / 1000000000000000000)) * (126 / 100) + 8 * ((334279201 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13190) *
          (32 * (((4168852951 / 1000000000000000000) : ℝ) + (13907997 / 10000000000000000) + (334279201 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13190 : ℝ) ^ 16 *
      (d.w0 13190 166 + d.w1 13190 166 * √(π / 2) + 2 * d.w2 13190 166 +
        energyR16 13190 * radiusPolynomialRoot16 (d.w0 13190 166) (d.w1 13190 166)
          (d.w2 13190 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13190 : ℝ) ^ 16 *
        (((818189599 / 50000000000000000000) : ℝ) + ((116425247 / 10000000000000000000)) * (126 / 100) + 2 * ((26586737 / 6250000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13190) *
          (32 * (((818189599 / 50000000000000000000) : ℝ) + (116425247 / 10000000000000000000) + (26586737 / 6250000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13190

/-! A coarse bound on the actual paper statistics constant at dimension 13191. -/
namespace BstLean.Part266.Row13191
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13189 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13189 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13189 128 ≤ (13443 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13443 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13191) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13191 : ℕ))
    (by norm_num : (13191 : ℕ) ≤ 16384)
  have ht : paperTail256 13191 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13191 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13191 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13191 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13191 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13191 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13189 128 * √(2 / (13191 : ℝ)) *
      (√(13191 : ℝ) + paperT0 13191 + paperTail256 13191) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13191 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13191 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13191 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13189 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13189 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13191 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13191

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13191
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13191 (61 / 100) 166 (17 / (100 * 13191)) (26 / (10 * 13191)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13191 (61 / 100) 166 (17 / (100 * 13191)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (425287393 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (644814493 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1886097167 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13191 / 13191 * (61 / 100)) ^ 4 * inverseRadius8 (13191 - 1) /
            envelopeGap 13191 (61 / 100) 166 (17 / (100 * 13191)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13191

namespace BstLean.Part266.Row13191
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13191 166 ≤ (2084031287 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13191 166 ≤ (278107209 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (334215839 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13191 166 ≤ (1636006993 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13191 166 ≤ (581993833 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13191 166 ≤ (53161381 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (425287393 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (425287393 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (644814493 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1886097167 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1794963 / 500000000) : ℝ) ≤ √(17 / (100 * 13191) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13191) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1031124863 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (35911404679 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13191) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13191) ≤ (10721049 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13191) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13191 * (166 : ℝ) ^ 2 + 26 / (10 * 13191) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13191) : ℝ)) (tA 13191 * 166 ^ 2 + 26 / (10 * 13191)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1794963 / 500000000))) * ((425287393 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1794963 / 500000000)) ^ 3) * ((644814493 / 500000000000000000000000))) + ((1886097167 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1794963 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13191) : ℝ)) d.D d.V d.P (√(tA 13191) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1794963 / 500000000)) ^ 2 * (((1031124863 / 500000000000000)) * ((35911404679 / 1000000000000000000)))) + ((1886097167 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13191) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1794963 / 500000000)) * ((425287393 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13191) : ℝ)) (tA 13191 * 166 ^ 2 + 26 / (10 * 13191)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((425287393 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1794963 / 500000000)) ^ 2) * ((644814493 / 500000000000000000000000)) + ((1886097167 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13191) : ℝ)) (√(26 / (10 * 13191) : ℝ)) d.D d.V d.P (√(tA 13191) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1794963 / 500000000)) * (((1031124863 / 500000000000000)) * ((35911404679 / 1000000000000000000))) + ((1886097167 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13191) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((425287393 / 100000000000000000000) : ℝ) + ((1886097167 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13191

namespace BstLean.Part266.Row13191
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13191 166 ∧
    0 ≤ (tableEnvelope C).f1 13191 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13191 166 ∧
    0 ≤ (tableEnvelope C).w1 13191 166 ∧ 0 ≤ (tableEnvelope C).w2 13191 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13191 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13191 166 ∧ 0 ≤ d.f1 13191 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13191 166 ∧ 0 ≤ d.w1 13191 166 ∧ 0 ≤ d.w2 13191 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13191 ≤ 2 * (228 / 100 : ℝ) / 13191 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13191 ≤ 2 * (370 / 100 : ℝ) / 13191 := by
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
    (completeRAData (tableEnvelope C) 13191 166).locationBound 13191 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13191 166).energyBound 13191 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13191 166) (d.f1 13191 166) d.f2 ≤
      32 * (((2084031287 / 500000000000000000) : ℝ) + (278107209 / 200000000000000000) + (334215839 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13191 166) (d.w1 13191 166)
      (d.w2 13191 166) ≤
      32 * (((1636006993 / 100000000000000000000) : ℝ) + (581993833 / 50000000000000000000) + (53161381 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13191 166) (d.f1 13191 166) d.f2 ≤
      ((2084031287 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2084031287 / 500000000000000000)) * ((278107209 / 200000000000000000)) * (126 / 100) +
      2 * (((278107209 / 200000000000000000)) ^ 2 + 2 * ((2084031287 / 500000000000000000)) * ((334215839 / 1000000000000000000))) +
      6 * ((278107209 / 200000000000000000)) * ((334215839 / 1000000000000000000)) * (126 / 100) + 8 * ((334215839 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13191 166) (d.f1 13191 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13191 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13191 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13191 166) (d.f1 13191 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13191 166) (d.w1 13191 166) (d.w2 13191 166)
  have hwexpr0 : 0 ≤ d.w0 13191 166 + d.w1 13191 166 * √(π / 2) +
      2 * d.w2 13191 166 + energyR16 13191 *
      radiusPolynomialRoot16 (d.w0 13191 166) (d.w1 13191 166) (d.w2 13191 166) := by
    positivity
  constructor
  · change (13191 : ℝ) ^ 8 * (mA 13191 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13191 166) (d.f1 13191 166) d.f2 + locationR16 13191 *
        radiusPolynomialRoot16 (d.f0 13191 166) (d.f1 13191 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13191 : ℝ) ^ 8 * (mA 13191 : ℝ) ^ 8 *
        ((((2084031287 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2084031287 / 500000000000000000)) * ((278107209 / 200000000000000000)) * (126 / 100) +
          2 * (((278107209 / 200000000000000000)) ^ 2 + 2 * ((2084031287 / 500000000000000000)) * ((334215839 / 1000000000000000000))) +
          6 * ((278107209 / 200000000000000000)) * ((334215839 / 1000000000000000000)) * (126 / 100) + 8 * ((334215839 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13191) *
          (32 * (((2084031287 / 500000000000000000) : ℝ) + (278107209 / 200000000000000000) + (334215839 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13191 : ℝ) ^ 16 *
      (d.w0 13191 166 + d.w1 13191 166 * √(π / 2) + 2 * d.w2 13191 166 +
        energyR16 13191 * radiusPolynomialRoot16 (d.w0 13191 166) (d.w1 13191 166)
          (d.w2 13191 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13191 : ℝ) ^ 16 *
        (((1636006993 / 100000000000000000000) : ℝ) + ((581993833 / 50000000000000000000)) * (126 / 100) + 2 * ((53161381 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13191) *
          (32 * (((1636006993 / 100000000000000000000) : ℝ) + (581993833 / 50000000000000000000) + (53161381 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13191

/-! A coarse bound on the actual paper statistics constant at dimension 13192. -/
namespace BstLean.Part266.Row13192
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13190 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13190 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13190 128 ≤ (13444 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13444 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13192) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13192 : ℕ))
    (by norm_num : (13192 : ℕ) ≤ 16384)
  have ht : paperTail256 13192 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13192 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13192 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13192 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13192 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13192 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13190 128 * √(2 / (13192 : ℝ)) *
      (√(13192 : ℝ) + paperT0 13192 + paperTail256 13192) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13192 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13192 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13192 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13190 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13190 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13192 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13192

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13192
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13192 (61 / 100) 166 (17 / (100 * 13192)) (26 / (10 * 13192)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13192 (61 / 100) 166 (17 / (100 * 13192)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (425190681 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (644618991 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3769885971 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13192 / 13192 * (61 / 100)) ^ 4 * inverseRadius8 (13192 - 1) /
            envelopeGap 13192 (61 / 100) 166 (17 / (100 * 13192)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13192

namespace BstLean.Part266.Row13192
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13192 166 ≤ (2083636231 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13192 166 ≤ (695136237 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (20884531 / 62500000000000000)
  w0 : (tableEnvelope C).w0 13192 166 ≤ (51113591 / 3125000000000000000)
  w1 : (tableEnvelope C).w1 13192 166 ≤ (290930737 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 13192 166 ≤ (425194333 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (425190681 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (425190681 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (644618991 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3769885971 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((358979 / 100000000) : ℝ) ≤ √(17 / (100 * 13192) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13192) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2062015231 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (17952980129 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13192) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13192) ≤ (107202363 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13192) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13192 * (166 : ℝ) ^ 2 + 26 / (10 * 13192) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13192) : ℝ)) (tA 13192 * 166 ^ 2 + 26 / (10 * 13192)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((358979 / 100000000))) * ((425190681 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((358979 / 100000000)) ^ 3) * ((644618991 / 500000000000000000000000))) + ((3769885971 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((358979 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13192) : ℝ)) d.D d.V d.P (√(tA 13192) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((358979 / 100000000)) ^ 2 * (((2062015231 / 1000000000000000)) * ((17952980129 / 500000000000000000)))) + ((3769885971 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13192) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((358979 / 100000000)) * ((425190681 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13192) : ℝ)) (tA 13192 * 166 ^ 2 + 26 / (10 * 13192)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((425190681 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((358979 / 100000000)) ^ 2) * ((644618991 / 500000000000000000000000)) + ((3769885971 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13192) : ℝ)) (√(26 / (10 * 13192) : ℝ)) d.D d.V d.P (√(tA 13192) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((358979 / 100000000)) * (((2062015231 / 1000000000000000)) * ((17952980129 / 500000000000000000))) + ((3769885971 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13192) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((425190681 / 100000000000000000000) : ℝ) + ((3769885971 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13192

namespace BstLean.Part266.Row13192
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13192 166 ∧
    0 ≤ (tableEnvelope C).f1 13192 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13192 166 ∧
    0 ≤ (tableEnvelope C).w1 13192 166 ∧ 0 ≤ (tableEnvelope C).w2 13192 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13192 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13192 166 ∧ 0 ≤ d.f1 13192 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13192 166 ∧ 0 ≤ d.w1 13192 166 ∧ 0 ≤ d.w2 13192 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13192 ≤ 2 * (228 / 100 : ℝ) / 13192 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13192 ≤ 2 * (370 / 100 : ℝ) / 13192 := by
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
    (completeRAData (tableEnvelope C) 13192 166).locationBound 13192 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13192 166).energyBound 13192 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13192 166) (d.f1 13192 166) d.f2 ≤
      32 * (((2083636231 / 500000000000000000) : ℝ) + (695136237 / 500000000000000000) + (20884531 / 62500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13192 166) (d.w1 13192 166)
      (d.w2 13192 166) ≤
      32 * (((51113591 / 3125000000000000000) : ℝ) + (290930737 / 25000000000000000000) + (425194333 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13192 166) (d.f1 13192 166) d.f2 ≤
      ((2083636231 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2083636231 / 500000000000000000)) * ((695136237 / 500000000000000000)) * (126 / 100) +
      2 * (((695136237 / 500000000000000000)) ^ 2 + 2 * ((2083636231 / 500000000000000000)) * ((20884531 / 62500000000000000))) +
      6 * ((695136237 / 500000000000000000)) * ((20884531 / 62500000000000000)) * (126 / 100) + 8 * ((20884531 / 62500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13192 166) (d.f1 13192 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13192 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13192 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13192 166) (d.f1 13192 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13192 166) (d.w1 13192 166) (d.w2 13192 166)
  have hwexpr0 : 0 ≤ d.w0 13192 166 + d.w1 13192 166 * √(π / 2) +
      2 * d.w2 13192 166 + energyR16 13192 *
      radiusPolynomialRoot16 (d.w0 13192 166) (d.w1 13192 166) (d.w2 13192 166) := by
    positivity
  constructor
  · change (13192 : ℝ) ^ 8 * (mA 13192 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13192 166) (d.f1 13192 166) d.f2 + locationR16 13192 *
        radiusPolynomialRoot16 (d.f0 13192 166) (d.f1 13192 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13192 : ℝ) ^ 8 * (mA 13192 : ℝ) ^ 8 *
        ((((2083636231 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2083636231 / 500000000000000000)) * ((695136237 / 500000000000000000)) * (126 / 100) +
          2 * (((695136237 / 500000000000000000)) ^ 2 + 2 * ((2083636231 / 500000000000000000)) * ((20884531 / 62500000000000000))) +
          6 * ((695136237 / 500000000000000000)) * ((20884531 / 62500000000000000)) * (126 / 100) + 8 * ((20884531 / 62500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13192) *
          (32 * (((2083636231 / 500000000000000000) : ℝ) + (695136237 / 500000000000000000) + (20884531 / 62500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13192 : ℝ) ^ 16 *
      (d.w0 13192 166 + d.w1 13192 166 * √(π / 2) + 2 * d.w2 13192 166 +
        energyR16 13192 * radiusPolynomialRoot16 (d.w0 13192 166) (d.w1 13192 166)
          (d.w2 13192 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13192 : ℝ) ^ 16 *
        (((51113591 / 3125000000000000000) : ℝ) + ((290930737 / 25000000000000000000)) * (126 / 100) + 2 * ((425194333 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13192) *
          (32 * (((51113591 / 3125000000000000000) : ℝ) + (290930737 / 25000000000000000000) + (425194333 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13192

/-! A coarse bound on the actual paper statistics constant at dimension 13193. -/
namespace BstLean.Part266.Row13193
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13191 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13191 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13191 128 ≤ (13445 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13445 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13193) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13193 : ℕ))
    (by norm_num : (13193 : ℕ) ≤ 16384)
  have ht : paperTail256 13193 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13193 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13193 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13193 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13193 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13193 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13191 128 * √(2 / (13193 : ℝ)) *
      (√(13193 : ℝ) + paperT0 13193 + paperTail256 13193) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13193 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13193 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13193 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13191 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13191 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13193 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13193

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13193
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13193 (61 / 100) 166 (17 / (100 * 13193)) (26 / (10 * 13193)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13193 (61 / 100) 166 (17 / (100 * 13193)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (212546999 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (644423563 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1883789599 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13193 / 13193 * (61 / 100)) ^ 4 * inverseRadius8 (13193 - 1) /
            envelopeGap 13193 (61 / 100) 166 (17 / (100 * 13193)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13193

namespace BstLean.Part266.Row13193
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13193 166 ≤ (4166482611 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13193 166 ≤ (173751123 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (334089171 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13193 166 ≤ (1635262953 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13193 166 ≤ (581729157 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13193 166 ≤ (26568603 / 6250000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (212546999 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (212546999 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (644423563 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1883789599 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1794827 / 500000000) : ℝ) ≤ √(17 / (100 * 13193) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13193) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2061780779 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (2243782317 / 62500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13193) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13193) ≤ (107194237 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13193) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13193 * (166 : ℝ) ^ 2 + 26 / (10 * 13193) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13193) : ℝ)) (tA 13193 * 166 ^ 2 + 26 / (10 * 13193)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1794827 / 500000000))) * ((212546999 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1794827 / 500000000)) ^ 3) * ((644423563 / 500000000000000000000000))) + ((1883789599 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1794827 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13193) : ℝ)) d.D d.V d.P (√(tA 13193) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1794827 / 500000000)) ^ 2 * (((2061780779 / 1000000000000000)) * ((2243782317 / 62500000000000000)))) + ((1883789599 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13193) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1794827 / 500000000)) * ((212546999 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13193) : ℝ)) (tA 13193 * 166 ^ 2 + 26 / (10 * 13193)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((212546999 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1794827 / 500000000)) ^ 2) * ((644423563 / 500000000000000000000000)) + ((1883789599 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13193) : ℝ)) (√(26 / (10 * 13193) : ℝ)) d.D d.V d.P (√(tA 13193) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1794827 / 500000000)) * (((2061780779 / 1000000000000000)) * ((2243782317 / 62500000000000000))) + ((1883789599 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13193) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((212546999 / 50000000000000000000) : ℝ) + ((1883789599 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13193

namespace BstLean.Part266.Row13193
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13193 166 ∧
    0 ≤ (tableEnvelope C).f1 13193 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13193 166 ∧
    0 ≤ (tableEnvelope C).w1 13193 166 ∧ 0 ≤ (tableEnvelope C).w2 13193 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13193 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13193 166 ∧ 0 ≤ d.f1 13193 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13193 166 ∧ 0 ≤ d.w1 13193 166 ∧ 0 ≤ d.w2 13193 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13193 ≤ 2 * (228 / 100 : ℝ) / 13193 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13193 ≤ 2 * (370 / 100 : ℝ) / 13193 := by
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
    (completeRAData (tableEnvelope C) 13193 166).locationBound 13193 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13193 166).energyBound 13193 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13193 166) (d.f1 13193 166) d.f2 ≤
      32 * (((4166482611 / 1000000000000000000) : ℝ) + (173751123 / 125000000000000000) + (334089171 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13193 166) (d.w1 13193 166)
      (d.w2 13193 166) ≤
      32 * (((1635262953 / 100000000000000000000) : ℝ) + (581729157 / 50000000000000000000) + (26568603 / 6250000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13193 166) (d.f1 13193 166) d.f2 ≤
      ((4166482611 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4166482611 / 1000000000000000000)) * ((173751123 / 125000000000000000)) * (126 / 100) +
      2 * (((173751123 / 125000000000000000)) ^ 2 + 2 * ((4166482611 / 1000000000000000000)) * ((334089171 / 1000000000000000000))) +
      6 * ((173751123 / 125000000000000000)) * ((334089171 / 1000000000000000000)) * (126 / 100) + 8 * ((334089171 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13193 166) (d.f1 13193 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13193 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13193 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13193 166) (d.f1 13193 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13193 166) (d.w1 13193 166) (d.w2 13193 166)
  have hwexpr0 : 0 ≤ d.w0 13193 166 + d.w1 13193 166 * √(π / 2) +
      2 * d.w2 13193 166 + energyR16 13193 *
      radiusPolynomialRoot16 (d.w0 13193 166) (d.w1 13193 166) (d.w2 13193 166) := by
    positivity
  constructor
  · change (13193 : ℝ) ^ 8 * (mA 13193 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13193 166) (d.f1 13193 166) d.f2 + locationR16 13193 *
        radiusPolynomialRoot16 (d.f0 13193 166) (d.f1 13193 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13193 : ℝ) ^ 8 * (mA 13193 : ℝ) ^ 8 *
        ((((4166482611 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4166482611 / 1000000000000000000)) * ((173751123 / 125000000000000000)) * (126 / 100) +
          2 * (((173751123 / 125000000000000000)) ^ 2 + 2 * ((4166482611 / 1000000000000000000)) * ((334089171 / 1000000000000000000))) +
          6 * ((173751123 / 125000000000000000)) * ((334089171 / 1000000000000000000)) * (126 / 100) + 8 * ((334089171 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13193) *
          (32 * (((4166482611 / 1000000000000000000) : ℝ) + (173751123 / 125000000000000000) + (334089171 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13193 : ℝ) ^ 16 *
      (d.w0 13193 166 + d.w1 13193 166 * √(π / 2) + 2 * d.w2 13193 166 +
        energyR16 13193 * radiusPolynomialRoot16 (d.w0 13193 166) (d.w1 13193 166)
          (d.w2 13193 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13193 : ℝ) ^ 16 *
        (((1635262953 / 100000000000000000000) : ℝ) + ((581729157 / 50000000000000000000)) * (126 / 100) + 2 * ((26568603 / 6250000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13193) *
          (32 * (((1635262953 / 100000000000000000000) : ℝ) + (581729157 / 50000000000000000000) + (26568603 / 6250000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13193

/-! A coarse bound on the actual paper statistics constant at dimension 13194. -/
namespace BstLean.Part266.Row13194
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13192 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13192 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13192 128 ≤ (13446 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13446 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13194) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13194 : ℕ))
    (by norm_num : (13194 : ℕ) ≤ 16384)
  have ht : paperTail256 13194 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13194 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13194 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13194 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13194 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13194 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13192 128 * √(2 / (13194 : ℝ)) *
      (√(13194 : ℝ) + paperT0 13194 + paperTail256 13194) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13194 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13194 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13194 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13192 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13192 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13194 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13194

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13194
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13194 (61 / 100) 166 (17 / (100 * 13194)) (26 / (10 * 13194)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13194 (61 / 100) 166 (17 / (100 * 13194)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (13281167 / 3125000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1288456419 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (753054803 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13194 / 13194 * (61 / 100)) ^ 4 * inverseRadius8 (13194 - 1) /
            envelopeGap 13194 (61 / 100) 166 (17 / (100 * 13194)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13194

namespace BstLean.Part266.Row13194
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13194 166 ≤ (4165693023 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13194 166 ≤ (173718197 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (41753233 / 125000000000000000)
  w0 : (tableEnvelope C).w0 13194 166 ≤ (1634891119 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13194 166 ≤ (1163193767 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13194 166 ≤ (13281281 / 3125000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (13281167 / 3125000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (13281167 / 3125000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1288456419 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (753054803 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1794759 / 500000000) : ℝ) ≤ √(17 / (100 * 13194) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13194) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (515386593 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (560860549 / 15625000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13194) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13194) ≤ (107186113 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13194) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13194 * (166 : ℝ) ^ 2 + 26 / (10 * 13194) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13194) : ℝ)) (tA 13194 * 166 ^ 2 + 26 / (10 * 13194)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1794759 / 500000000))) * ((13281167 / 3125000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1794759 / 500000000)) ^ 3) * ((1288456419 / 1000000000000000000000000))) + ((753054803 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1794759 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13194) : ℝ)) d.D d.V d.P (√(tA 13194) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1794759 / 500000000)) ^ 2 * (((515386593 / 250000000000000)) * ((560860549 / 15625000000000000)))) + ((753054803 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13194) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1794759 / 500000000)) * ((13281167 / 3125000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13194) : ℝ)) (tA 13194 * 166 ^ 2 + 26 / (10 * 13194)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((13281167 / 3125000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1794759 / 500000000)) ^ 2) * ((1288456419 / 1000000000000000000000000)) + ((753054803 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13194) : ℝ)) (√(26 / (10 * 13194) : ℝ)) d.D d.V d.P (√(tA 13194) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1794759 / 500000000)) * (((515386593 / 250000000000000)) * ((560860549 / 15625000000000000))) + ((753054803 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13194) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((13281167 / 3125000000000000000) : ℝ) + ((753054803 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13194

namespace BstLean.Part266.Row13194
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13194 166 ∧
    0 ≤ (tableEnvelope C).f1 13194 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13194 166 ∧
    0 ≤ (tableEnvelope C).w1 13194 166 ∧ 0 ≤ (tableEnvelope C).w2 13194 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13194 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13194 166 ∧ 0 ≤ d.f1 13194 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13194 166 ∧ 0 ≤ d.w1 13194 166 ∧ 0 ≤ d.w2 13194 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13194 ≤ 2 * (228 / 100 : ℝ) / 13194 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13194 ≤ 2 * (370 / 100 : ℝ) / 13194 := by
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
    (completeRAData (tableEnvelope C) 13194 166).locationBound 13194 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13194 166).energyBound 13194 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13194 166) (d.f1 13194 166) d.f2 ≤
      32 * (((4165693023 / 1000000000000000000) : ℝ) + (173718197 / 125000000000000000) + (41753233 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13194 166) (d.w1 13194 166)
      (d.w2 13194 166) ≤
      32 * (((1634891119 / 100000000000000000000) : ℝ) + (1163193767 / 100000000000000000000) + (13281281 / 3125000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13194 166) (d.f1 13194 166) d.f2 ≤
      ((4165693023 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4165693023 / 1000000000000000000)) * ((173718197 / 125000000000000000)) * (126 / 100) +
      2 * (((173718197 / 125000000000000000)) ^ 2 + 2 * ((4165693023 / 1000000000000000000)) * ((41753233 / 125000000000000000))) +
      6 * ((173718197 / 125000000000000000)) * ((41753233 / 125000000000000000)) * (126 / 100) + 8 * ((41753233 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13194 166) (d.f1 13194 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13194 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13194 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13194 166) (d.f1 13194 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13194 166) (d.w1 13194 166) (d.w2 13194 166)
  have hwexpr0 : 0 ≤ d.w0 13194 166 + d.w1 13194 166 * √(π / 2) +
      2 * d.w2 13194 166 + energyR16 13194 *
      radiusPolynomialRoot16 (d.w0 13194 166) (d.w1 13194 166) (d.w2 13194 166) := by
    positivity
  constructor
  · change (13194 : ℝ) ^ 8 * (mA 13194 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13194 166) (d.f1 13194 166) d.f2 + locationR16 13194 *
        radiusPolynomialRoot16 (d.f0 13194 166) (d.f1 13194 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13194 : ℝ) ^ 8 * (mA 13194 : ℝ) ^ 8 *
        ((((4165693023 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4165693023 / 1000000000000000000)) * ((173718197 / 125000000000000000)) * (126 / 100) +
          2 * (((173718197 / 125000000000000000)) ^ 2 + 2 * ((4165693023 / 1000000000000000000)) * ((41753233 / 125000000000000000))) +
          6 * ((173718197 / 125000000000000000)) * ((41753233 / 125000000000000000)) * (126 / 100) + 8 * ((41753233 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13194) *
          (32 * (((4165693023 / 1000000000000000000) : ℝ) + (173718197 / 125000000000000000) + (41753233 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13194 : ℝ) ^ 16 *
      (d.w0 13194 166 + d.w1 13194 166 * √(π / 2) + 2 * d.w2 13194 166 +
        energyR16 13194 * radiusPolynomialRoot16 (d.w0 13194 166) (d.w1 13194 166)
          (d.w2 13194 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13194 : ℝ) ^ 16 *
        (((1634891119 / 100000000000000000000) : ℝ) + ((1163193767 / 100000000000000000000)) * (126 / 100) + 2 * ((13281281 / 3125000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13194) *
          (32 * (((1634891119 / 100000000000000000000) : ℝ) + (1163193767 / 100000000000000000000) + (13281281 / 3125000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13194

/-! A coarse bound on the actual paper statistics constant at dimension 13195. -/
namespace BstLean.Part266.Row13195
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13193 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13193 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13193 128 ≤ (13447 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13447 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13195) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13195 : ℕ))
    (by norm_num : (13195 : ℕ) ≤ 16384)
  have ht : paperTail256 13195 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13195 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13195 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13195 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13195 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13195 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13193 128 * √(2 / (13195 : ℝ)) *
      (√(13195 : ℝ) + paperT0 13195 + paperTail256 13195) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13195 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13195 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13195 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13193 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13193 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13195 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13195

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13195
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13195 (61 / 100) 166 (17 / (100 * 13195)) (26 / (10 * 13195)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13195 (61 / 100) 166 (17 / (100 * 13195)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (5311259 / 1250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1288065859 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3762970421 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13195 / 13195 * (61 / 100)) ^ 4 * inverseRadius8 (13195 - 1) /
            envelopeGap 13195 (61 / 100) 166 (17 / (100 * 13195)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13195

namespace BstLean.Part266.Row13195
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13195 166 ≤ (2082451847 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13195 166 ≤ (5557929 / 4000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (20872661 / 62500000000000000)
  w0 : (tableEnvelope C).w0 13195 166 ≤ (1634519407 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13195 166 ≤ (232585861 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 13195 166 ≤ (212452183 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (5311259 / 1250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (5311259 / 1250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1288065859 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3762970421 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1794691 / 500000000) : ℝ) ≤ √(17 / (100 * 13195) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13195) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (206131201 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (35889634423 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13195) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13195) ≤ (107177989 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13195) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13195 * (166 : ℝ) ^ 2 + 26 / (10 * 13195) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13195) : ℝ)) (tA 13195 * 166 ^ 2 + 26 / (10 * 13195)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1794691 / 500000000))) * ((5311259 / 1250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1794691 / 500000000)) ^ 3) * ((1288065859 / 1000000000000000000000000))) + ((3762970421 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1794691 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13195) : ℝ)) d.D d.V d.P (√(tA 13195) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1794691 / 500000000)) ^ 2 * (((206131201 / 100000000000000)) * ((35889634423 / 1000000000000000000)))) + ((3762970421 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13195) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1794691 / 500000000)) * ((5311259 / 1250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13195) : ℝ)) (tA 13195 * 166 ^ 2 + 26 / (10 * 13195)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((5311259 / 1250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1794691 / 500000000)) ^ 2) * ((1288065859 / 1000000000000000000000000)) + ((3762970421 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13195) : ℝ)) (√(26 / (10 * 13195) : ℝ)) d.D d.V d.P (√(tA 13195) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1794691 / 500000000)) * (((206131201 / 100000000000000)) * ((35889634423 / 1000000000000000000))) + ((3762970421 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13195) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((5311259 / 1250000000000000000) : ℝ) + ((3762970421 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13195

namespace BstLean.Part266.Row13195
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13195 166 ∧
    0 ≤ (tableEnvelope C).f1 13195 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13195 166 ∧
    0 ≤ (tableEnvelope C).w1 13195 166 ∧ 0 ≤ (tableEnvelope C).w2 13195 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13195 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13195 166 ∧ 0 ≤ d.f1 13195 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13195 166 ∧ 0 ≤ d.w1 13195 166 ∧ 0 ≤ d.w2 13195 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13195 ≤ 2 * (228 / 100 : ℝ) / 13195 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13195 ≤ 2 * (370 / 100 : ℝ) / 13195 := by
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
    (completeRAData (tableEnvelope C) 13195 166).locationBound 13195 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13195 166).energyBound 13195 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13195 166) (d.f1 13195 166) d.f2 ≤
      32 * (((2082451847 / 500000000000000000) : ℝ) + (5557929 / 4000000000000000) + (20872661 / 62500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13195 166) (d.w1 13195 166)
      (d.w2 13195 166) ≤
      32 * (((1634519407 / 100000000000000000000) : ℝ) + (232585861 / 20000000000000000000) + (212452183 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13195 166) (d.f1 13195 166) d.f2 ≤
      ((2082451847 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2082451847 / 500000000000000000)) * ((5557929 / 4000000000000000)) * (126 / 100) +
      2 * (((5557929 / 4000000000000000)) ^ 2 + 2 * ((2082451847 / 500000000000000000)) * ((20872661 / 62500000000000000))) +
      6 * ((5557929 / 4000000000000000)) * ((20872661 / 62500000000000000)) * (126 / 100) + 8 * ((20872661 / 62500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13195 166) (d.f1 13195 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13195 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13195 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13195 166) (d.f1 13195 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13195 166) (d.w1 13195 166) (d.w2 13195 166)
  have hwexpr0 : 0 ≤ d.w0 13195 166 + d.w1 13195 166 * √(π / 2) +
      2 * d.w2 13195 166 + energyR16 13195 *
      radiusPolynomialRoot16 (d.w0 13195 166) (d.w1 13195 166) (d.w2 13195 166) := by
    positivity
  constructor
  · change (13195 : ℝ) ^ 8 * (mA 13195 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13195 166) (d.f1 13195 166) d.f2 + locationR16 13195 *
        radiusPolynomialRoot16 (d.f0 13195 166) (d.f1 13195 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13195 : ℝ) ^ 8 * (mA 13195 : ℝ) ^ 8 *
        ((((2082451847 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2082451847 / 500000000000000000)) * ((5557929 / 4000000000000000)) * (126 / 100) +
          2 * (((5557929 / 4000000000000000)) ^ 2 + 2 * ((2082451847 / 500000000000000000)) * ((20872661 / 62500000000000000))) +
          6 * ((5557929 / 4000000000000000)) * ((20872661 / 62500000000000000)) * (126 / 100) + 8 * ((20872661 / 62500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13195) *
          (32 * (((2082451847 / 500000000000000000) : ℝ) + (5557929 / 4000000000000000) + (20872661 / 62500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13195 : ℝ) ^ 16 *
      (d.w0 13195 166 + d.w1 13195 166 * √(π / 2) + 2 * d.w2 13195 166 +
        energyR16 13195 * radiusPolynomialRoot16 (d.w0 13195 166) (d.w1 13195 166)
          (d.w2 13195 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13195 : ℝ) ^ 16 *
        (((1634519407 / 100000000000000000000) : ℝ) + ((232585861 / 20000000000000000000)) * (126 / 100) + 2 * ((212452183 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13195) *
          (32 * (((1634519407 / 100000000000000000000) : ℝ) + (232585861 / 20000000000000000000) + (212452183 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13195

/-! A coarse bound on the actual paper statistics constant at dimension 13196. -/
namespace BstLean.Part266.Row13196
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13194 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13194 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13194 128 ≤ (13448 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13448 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13196) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13196 : ℕ))
    (by norm_num : (13196 : ℕ) ≤ 16384)
  have ht : paperTail256 13196 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13196 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13196 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13196 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13196 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13196 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13194 128 * √(2 / (13196 : ℝ)) *
      (√(13196 : ℝ) + paperT0 13196 + paperTail256 13196) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13196 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13196 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13196 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13194 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13194 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13196 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13196

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13196
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13196 (61 / 100) 166 (17 / (100 * 13196)) (26 / (10 * 13196)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13196 (61 / 100) 166 (17 / (100 * 13196)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (106201031 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1287675447 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3760668413 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13196 / 13196 * (61 / 100)) ^ 4 * inverseRadius8 (13196 - 1) /
            envelopeGap 13196 (61 / 100) 166 (17 / (100 * 13196)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13196

namespace BstLean.Part266.Row13196
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13196 166 ≤ (33312917 / 8000000000000000)
  f1 : (tableEnvelope C).f1 13196 166 ≤ (347304751 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (66779861 / 200000000000000000)
  w0 : (tableEnvelope C).w0 13196 166 ≤ (1634147817 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13196 166 ≤ (581332463 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13196 166 ≤ (424807767 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (106201031 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (106201031 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1287675447 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3760668413 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1794623 / 500000000) : ℝ) ≤ √(17 / (100 * 13196) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13196) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2061077689 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (8971048737 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13196) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13196) ≤ (107169867 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13196) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13196 * (166 : ℝ) ^ 2 + 26 / (10 * 13196) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13196) : ℝ)) (tA 13196 * 166 ^ 2 + 26 / (10 * 13196)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1794623 / 500000000))) * ((106201031 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1794623 / 500000000)) ^ 3) * ((1287675447 / 1000000000000000000000000))) + ((3760668413 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1794623 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13196) : ℝ)) d.D d.V d.P (√(tA 13196) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1794623 / 500000000)) ^ 2 * (((2061077689 / 1000000000000000)) * ((8971048737 / 250000000000000000)))) + ((3760668413 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13196) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1794623 / 500000000)) * ((106201031 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13196) : ℝ)) (tA 13196 * 166 ^ 2 + 26 / (10 * 13196)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((106201031 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1794623 / 500000000)) ^ 2) * ((1287675447 / 1000000000000000000000000)) + ((3760668413 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13196) : ℝ)) (√(26 / (10 * 13196) : ℝ)) d.D d.V d.P (√(tA 13196) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1794623 / 500000000)) * (((2061077689 / 1000000000000000)) * ((8971048737 / 250000000000000000))) + ((3760668413 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13196) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((106201031 / 25000000000000000000) : ℝ) + ((3760668413 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13196

namespace BstLean.Part266.Row13196
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13196 166 ∧
    0 ≤ (tableEnvelope C).f1 13196 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13196 166 ∧
    0 ≤ (tableEnvelope C).w1 13196 166 ∧ 0 ≤ (tableEnvelope C).w2 13196 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13196 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13196 166 ∧ 0 ≤ d.f1 13196 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13196 166 ∧ 0 ≤ d.w1 13196 166 ∧ 0 ≤ d.w2 13196 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13196 ≤ 2 * (228 / 100 : ℝ) / 13196 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13196 ≤ 2 * (370 / 100 : ℝ) / 13196 := by
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
    (completeRAData (tableEnvelope C) 13196 166).locationBound 13196 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13196 166).energyBound 13196 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13196 166) (d.f1 13196 166) d.f2 ≤
      32 * (((33312917 / 8000000000000000) : ℝ) + (347304751 / 250000000000000000) + (66779861 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13196 166) (d.w1 13196 166)
      (d.w2 13196 166) ≤
      32 * (((1634147817 / 100000000000000000000) : ℝ) + (581332463 / 50000000000000000000) + (424807767 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13196 166) (d.f1 13196 166) d.f2 ≤
      ((33312917 / 8000000000000000) : ℝ) ^ 2 + 2 * ((33312917 / 8000000000000000)) * ((347304751 / 250000000000000000)) * (126 / 100) +
      2 * (((347304751 / 250000000000000000)) ^ 2 + 2 * ((33312917 / 8000000000000000)) * ((66779861 / 200000000000000000))) +
      6 * ((347304751 / 250000000000000000)) * ((66779861 / 200000000000000000)) * (126 / 100) + 8 * ((66779861 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13196 166) (d.f1 13196 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13196 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13196 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13196 166) (d.f1 13196 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13196 166) (d.w1 13196 166) (d.w2 13196 166)
  have hwexpr0 : 0 ≤ d.w0 13196 166 + d.w1 13196 166 * √(π / 2) +
      2 * d.w2 13196 166 + energyR16 13196 *
      radiusPolynomialRoot16 (d.w0 13196 166) (d.w1 13196 166) (d.w2 13196 166) := by
    positivity
  constructor
  · change (13196 : ℝ) ^ 8 * (mA 13196 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13196 166) (d.f1 13196 166) d.f2 + locationR16 13196 *
        radiusPolynomialRoot16 (d.f0 13196 166) (d.f1 13196 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13196 : ℝ) ^ 8 * (mA 13196 : ℝ) ^ 8 *
        ((((33312917 / 8000000000000000) : ℝ) ^ 2 + 2 * ((33312917 / 8000000000000000)) * ((347304751 / 250000000000000000)) * (126 / 100) +
          2 * (((347304751 / 250000000000000000)) ^ 2 + 2 * ((33312917 / 8000000000000000)) * ((66779861 / 200000000000000000))) +
          6 * ((347304751 / 250000000000000000)) * ((66779861 / 200000000000000000)) * (126 / 100) + 8 * ((66779861 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13196) *
          (32 * (((33312917 / 8000000000000000) : ℝ) + (347304751 / 250000000000000000) + (66779861 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13196 : ℝ) ^ 16 *
      (d.w0 13196 166 + d.w1 13196 166 * √(π / 2) + 2 * d.w2 13196 166 +
        energyR16 13196 * radiusPolynomialRoot16 (d.w0 13196 166) (d.w1 13196 166)
          (d.w2 13196 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13196 : ℝ) ^ 16 *
        (((1634147817 / 100000000000000000000) : ℝ) + ((581332463 / 50000000000000000000)) * (126 / 100) + 2 * ((424807767 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13196) *
          (32 * (((1634147817 / 100000000000000000000) : ℝ) + (581332463 / 50000000000000000000) + (424807767 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13196

/-! A coarse bound on the actual paper statistics constant at dimension 13197. -/
namespace BstLean.Part266.Row13197
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13195 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13195 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13195 128 ≤ (13449 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13449 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13197) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13197 : ℕ))
    (by norm_num : (13197 : ℕ) ≤ 16384)
  have ht : paperTail256 13197 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13197 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13197 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13197 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13197 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13197 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13195 128 * √(2 / (13197 : ℝ)) *
      (√(13197 : ℝ) + paperT0 13197 + paperTail256 13197) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13197 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13197 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13197 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13195 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13195 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13197 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13197

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13197
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13197 (61 / 100) 166 (17 / (100 * 13197)) (26 / (10 * 13197)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13197 (61 / 100) 166 (17 / (100 * 13197)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (424707559 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (20113831 / 15625000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3758367991 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13197 / 13197 * (61 / 100)) ^ 4 * inverseRadius8 (13197 - 1) /
            envelopeGap 13197 (61 / 100) 166 (17 / (100 * 13197)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13197

namespace BstLean.Part266.Row13197
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13197 166 ≤ (2081662911 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13197 166 ≤ (347238961 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (333836053 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13197 166 ≤ (1633776353 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13197 166 ≤ (232480127 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 13197 166 ≤ (530889 / 125000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (424707559 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (424707559 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (20113831 / 15625000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3758367991 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((358911 / 100000000) : ℝ) ≤ √(17 / (100 * 13197) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13197) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1030421709 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (8969689181 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13197) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13197) ≤ (107161747 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13197) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13197 * (166 : ℝ) ^ 2 + 26 / (10 * 13197) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13197) : ℝ)) (tA 13197 * 166 ^ 2 + 26 / (10 * 13197)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((358911 / 100000000))) * ((424707559 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((358911 / 100000000)) ^ 3) * ((20113831 / 15625000000000000000000))) + ((3758367991 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((358911 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13197) : ℝ)) d.D d.V d.P (√(tA 13197) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((358911 / 100000000)) ^ 2 * (((1030421709 / 500000000000000)) * ((8969689181 / 250000000000000000)))) + ((3758367991 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13197) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((358911 / 100000000)) * ((424707559 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13197) : ℝ)) (tA 13197 * 166 ^ 2 + 26 / (10 * 13197)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((424707559 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((358911 / 100000000)) ^ 2) * ((20113831 / 15625000000000000000000)) + ((3758367991 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13197) : ℝ)) (√(26 / (10 * 13197) : ℝ)) d.D d.V d.P (√(tA 13197) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((358911 / 100000000)) * (((1030421709 / 500000000000000)) * ((8969689181 / 250000000000000000))) + ((3758367991 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13197) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((424707559 / 100000000000000000000) : ℝ) + ((3758367991 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13197

namespace BstLean.Part266.Row13197
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13197 166 ∧
    0 ≤ (tableEnvelope C).f1 13197 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13197 166 ∧
    0 ≤ (tableEnvelope C).w1 13197 166 ∧ 0 ≤ (tableEnvelope C).w2 13197 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13197 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13197 166 ∧ 0 ≤ d.f1 13197 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13197 166 ∧ 0 ≤ d.w1 13197 166 ∧ 0 ≤ d.w2 13197 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13197 ≤ 2 * (228 / 100 : ℝ) / 13197 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13197 ≤ 2 * (370 / 100 : ℝ) / 13197 := by
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
    (completeRAData (tableEnvelope C) 13197 166).locationBound 13197 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13197 166).energyBound 13197 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13197 166) (d.f1 13197 166) d.f2 ≤
      32 * (((2081662911 / 500000000000000000) : ℝ) + (347238961 / 250000000000000000) + (333836053 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13197 166) (d.w1 13197 166)
      (d.w2 13197 166) ≤
      32 * (((1633776353 / 100000000000000000000) : ℝ) + (232480127 / 20000000000000000000) + (530889 / 125000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13197 166) (d.f1 13197 166) d.f2 ≤
      ((2081662911 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2081662911 / 500000000000000000)) * ((347238961 / 250000000000000000)) * (126 / 100) +
      2 * (((347238961 / 250000000000000000)) ^ 2 + 2 * ((2081662911 / 500000000000000000)) * ((333836053 / 1000000000000000000))) +
      6 * ((347238961 / 250000000000000000)) * ((333836053 / 1000000000000000000)) * (126 / 100) + 8 * ((333836053 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13197 166) (d.f1 13197 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13197 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13197 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13197 166) (d.f1 13197 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13197 166) (d.w1 13197 166) (d.w2 13197 166)
  have hwexpr0 : 0 ≤ d.w0 13197 166 + d.w1 13197 166 * √(π / 2) +
      2 * d.w2 13197 166 + energyR16 13197 *
      radiusPolynomialRoot16 (d.w0 13197 166) (d.w1 13197 166) (d.w2 13197 166) := by
    positivity
  constructor
  · change (13197 : ℝ) ^ 8 * (mA 13197 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13197 166) (d.f1 13197 166) d.f2 + locationR16 13197 *
        radiusPolynomialRoot16 (d.f0 13197 166) (d.f1 13197 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13197 : ℝ) ^ 8 * (mA 13197 : ℝ) ^ 8 *
        ((((2081662911 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2081662911 / 500000000000000000)) * ((347238961 / 250000000000000000)) * (126 / 100) +
          2 * (((347238961 / 250000000000000000)) ^ 2 + 2 * ((2081662911 / 500000000000000000)) * ((333836053 / 1000000000000000000))) +
          6 * ((347238961 / 250000000000000000)) * ((333836053 / 1000000000000000000)) * (126 / 100) + 8 * ((333836053 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13197) *
          (32 * (((2081662911 / 500000000000000000) : ℝ) + (347238961 / 250000000000000000) + (333836053 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13197 : ℝ) ^ 16 *
      (d.w0 13197 166 + d.w1 13197 166 * √(π / 2) + 2 * d.w2 13197 166 +
        energyR16 13197 * radiusPolynomialRoot16 (d.w0 13197 166) (d.w1 13197 166)
          (d.w2 13197 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13197 : ℝ) ^ 16 *
        (((1633776353 / 100000000000000000000) : ℝ) + ((232480127 / 20000000000000000000)) * (126 / 100) + 2 * ((530889 / 125000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13197) *
          (32 * (((1633776353 / 100000000000000000000) : ℝ) + (232480127 / 20000000000000000000) + (530889 / 125000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13197

/-! A coarse bound on the actual paper statistics constant at dimension 13198. -/
namespace BstLean.Part266.Row13198
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13196 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13196 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13196 128 ≤ (13450 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13450 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13198) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13198 : ℕ))
    (by norm_num : (13198 : ℕ) ≤ 16384)
  have ht : paperTail256 13198 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13198 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13198 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13198 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13198 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13198 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13196 128 * √(2 / (13198 : ℝ)) *
      (√(13198 : ℝ) + paperT0 13198 + paperTail256 13198) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13198 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13198 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13198 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13196 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13196 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13198 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13198

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13198
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13198 (61 / 100) 166 (17 / (100 * 13198)) (26 / (10 * 13198)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13198 (61 / 100) 166 (17 / (100 * 13198)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (212305511 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (321723767 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3756069153 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13198 / 13198 * (61 / 100)) ^ 4 * inverseRadius8 (13198 - 1) /
            envelopeGap 13198 (61 / 100) 166 (17 / (100 * 13198)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13198

namespace BstLean.Part266.Row13198
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13198 166 ≤ (4162537277 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13198 166 ≤ (694346381 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (333772819 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13198 166 ≤ (163340501 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 13198 166 ≤ (1162136427 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13198 166 ≤ (424614661 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (212305511 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (212305511 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (321723767 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3756069153 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1794487 / 500000000) : ℝ) ≤ √(17 / (100 * 13198) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13198) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2060609187 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (8968329931 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13198) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13198) ≤ (107153627 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13198) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13198 * (166 : ℝ) ^ 2 + 26 / (10 * 13198) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13198) : ℝ)) (tA 13198 * 166 ^ 2 + 26 / (10 * 13198)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1794487 / 500000000))) * ((212305511 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1794487 / 500000000)) ^ 3) * ((321723767 / 250000000000000000000000))) + ((3756069153 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1794487 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13198) : ℝ)) d.D d.V d.P (√(tA 13198) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1794487 / 500000000)) ^ 2 * (((2060609187 / 1000000000000000)) * ((8968329931 / 250000000000000000)))) + ((3756069153 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13198) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1794487 / 500000000)) * ((212305511 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13198) : ℝ)) (tA 13198 * 166 ^ 2 + 26 / (10 * 13198)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((212305511 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1794487 / 500000000)) ^ 2) * ((321723767 / 250000000000000000000000)) + ((3756069153 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13198) : ℝ)) (√(26 / (10 * 13198) : ℝ)) d.D d.V d.P (√(tA 13198) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1794487 / 500000000)) * (((2060609187 / 1000000000000000)) * ((8968329931 / 250000000000000000))) + ((3756069153 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13198) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((212305511 / 50000000000000000000) : ℝ) + ((3756069153 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13198

namespace BstLean.Part266.Row13198
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13198 166 ∧
    0 ≤ (tableEnvelope C).f1 13198 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13198 166 ∧
    0 ≤ (tableEnvelope C).w1 13198 166 ∧ 0 ≤ (tableEnvelope C).w2 13198 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13198 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13198 166 ∧ 0 ≤ d.f1 13198 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13198 166 ∧ 0 ≤ d.w1 13198 166 ∧ 0 ≤ d.w2 13198 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13198 ≤ 2 * (228 / 100 : ℝ) / 13198 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13198 ≤ 2 * (370 / 100 : ℝ) / 13198 := by
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
    (completeRAData (tableEnvelope C) 13198 166).locationBound 13198 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13198 166).energyBound 13198 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13198 166) (d.f1 13198 166) d.f2 ≤
      32 * (((4162537277 / 1000000000000000000) : ℝ) + (694346381 / 500000000000000000) + (333772819 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13198 166) (d.w1 13198 166)
      (d.w2 13198 166) ≤
      32 * (((163340501 / 10000000000000000000) : ℝ) + (1162136427 / 100000000000000000000) + (424614661 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13198 166) (d.f1 13198 166) d.f2 ≤
      ((4162537277 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4162537277 / 1000000000000000000)) * ((694346381 / 500000000000000000)) * (126 / 100) +
      2 * (((694346381 / 500000000000000000)) ^ 2 + 2 * ((4162537277 / 1000000000000000000)) * ((333772819 / 1000000000000000000))) +
      6 * ((694346381 / 500000000000000000)) * ((333772819 / 1000000000000000000)) * (126 / 100) + 8 * ((333772819 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13198 166) (d.f1 13198 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13198 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13198 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13198 166) (d.f1 13198 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13198 166) (d.w1 13198 166) (d.w2 13198 166)
  have hwexpr0 : 0 ≤ d.w0 13198 166 + d.w1 13198 166 * √(π / 2) +
      2 * d.w2 13198 166 + energyR16 13198 *
      radiusPolynomialRoot16 (d.w0 13198 166) (d.w1 13198 166) (d.w2 13198 166) := by
    positivity
  constructor
  · change (13198 : ℝ) ^ 8 * (mA 13198 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13198 166) (d.f1 13198 166) d.f2 + locationR16 13198 *
        radiusPolynomialRoot16 (d.f0 13198 166) (d.f1 13198 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13198 : ℝ) ^ 8 * (mA 13198 : ℝ) ^ 8 *
        ((((4162537277 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4162537277 / 1000000000000000000)) * ((694346381 / 500000000000000000)) * (126 / 100) +
          2 * (((694346381 / 500000000000000000)) ^ 2 + 2 * ((4162537277 / 1000000000000000000)) * ((333772819 / 1000000000000000000))) +
          6 * ((694346381 / 500000000000000000)) * ((333772819 / 1000000000000000000)) * (126 / 100) + 8 * ((333772819 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13198) *
          (32 * (((4162537277 / 1000000000000000000) : ℝ) + (694346381 / 500000000000000000) + (333772819 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13198 : ℝ) ^ 16 *
      (d.w0 13198 166 + d.w1 13198 166 * √(π / 2) + 2 * d.w2 13198 166 +
        energyR16 13198 * radiusPolynomialRoot16 (d.w0 13198 166) (d.w1 13198 166)
          (d.w2 13198 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13198 : ℝ) ^ 16 *
        (((163340501 / 10000000000000000000) : ℝ) + ((1162136427 / 100000000000000000000)) * (126 / 100) + 2 * ((424614661 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13198) *
          (32 * (((163340501 / 10000000000000000000) : ℝ) + (1162136427 / 100000000000000000000) + (424614661 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13198

/-! A coarse bound on the actual paper statistics constant at dimension 13199. -/
namespace BstLean.Part266.Row13199
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13197 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13197 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13197 128 ≤ (13451 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13451 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13199) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13199 : ℕ))
    (by norm_num : (13199 : ℕ) ≤ 16384)
  have ht : paperTail256 13199 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13199 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13199 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13199 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13199 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13199 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13197 128 * √(2 / (13199 : ℝ)) *
      (√(13199 : ℝ) + paperT0 13199 + paperTail256 13199) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13199 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13199 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13199 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13197 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13197 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13199 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13199

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13199
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13199 (61 / 100) 166 (17 / (100 * 13199)) (26 / (10 * 13199)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13199 (61 / 100) 166 (17 / (100 * 13199)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (84902903 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1286505099 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3753771899 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13199 / 13199 * (61 / 100)) ^ 4 * inverseRadius8 (13199 - 1) /
            envelopeGap 13199 (61 / 100) 166 (17 / (100 * 13199)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13199

namespace BstLean.Part266.Row13199
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13199 166 ≤ (416174899 / 100000000000000000)
  f1 : (tableEnvelope C).f1 13199 166 ≤ (1388429763 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (83427401 / 250000000000000000)
  w0 : (tableEnvelope C).w0 13199 166 ≤ (163303379 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 13199 166 ≤ (580936153 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13199 166 ≤ (53064769 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (84902903 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (84902903 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1286505099 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3753771899 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1794419 / 500000000) : ℝ) ≤ √(17 / (100 * 13199) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13199) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2060375003 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (717357679 / 20000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13199) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13199) ≤ (107145509 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13199) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13199 * (166 : ℝ) ^ 2 + 26 / (10 * 13199) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13199) : ℝ)) (tA 13199 * 166 ^ 2 + 26 / (10 * 13199)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1794419 / 500000000))) * ((84902903 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1794419 / 500000000)) ^ 3) * ((1286505099 / 1000000000000000000000000))) + ((3753771899 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1794419 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13199) : ℝ)) d.D d.V d.P (√(tA 13199) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1794419 / 500000000)) ^ 2 * (((2060375003 / 1000000000000000)) * ((717357679 / 20000000000000000)))) + ((3753771899 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13199) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1794419 / 500000000)) * ((84902903 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13199) : ℝ)) (tA 13199 * 166 ^ 2 + 26 / (10 * 13199)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((84902903 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1794419 / 500000000)) ^ 2) * ((1286505099 / 1000000000000000000000000)) + ((3753771899 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13199) : ℝ)) (√(26 / (10 * 13199) : ℝ)) d.D d.V d.P (√(tA 13199) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1794419 / 500000000)) * (((2060375003 / 1000000000000000)) * ((717357679 / 20000000000000000))) + ((3753771899 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13199) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((84902903 / 20000000000000000000) : ℝ) + ((3753771899 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13199

namespace BstLean.Part266.Row13199
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13199 166 ∧
    0 ≤ (tableEnvelope C).f1 13199 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13199 166 ∧
    0 ≤ (tableEnvelope C).w1 13199 166 ∧ 0 ≤ (tableEnvelope C).w2 13199 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13199 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13199 166 ∧ 0 ≤ d.f1 13199 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13199 166 ∧ 0 ≤ d.w1 13199 166 ∧ 0 ≤ d.w2 13199 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13199 ≤ 2 * (228 / 100 : ℝ) / 13199 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13199 ≤ 2 * (370 / 100 : ℝ) / 13199 := by
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
    (completeRAData (tableEnvelope C) 13199 166).locationBound 13199 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13199 166).energyBound 13199 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13199 166) (d.f1 13199 166) d.f2 ≤
      32 * (((416174899 / 100000000000000000) : ℝ) + (1388429763 / 1000000000000000000) + (83427401 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13199 166) (d.w1 13199 166)
      (d.w2 13199 166) ≤
      32 * (((163303379 / 10000000000000000000) : ℝ) + (580936153 / 50000000000000000000) + (53064769 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13199 166) (d.f1 13199 166) d.f2 ≤
      ((416174899 / 100000000000000000) : ℝ) ^ 2 + 2 * ((416174899 / 100000000000000000)) * ((1388429763 / 1000000000000000000)) * (126 / 100) +
      2 * (((1388429763 / 1000000000000000000)) ^ 2 + 2 * ((416174899 / 100000000000000000)) * ((83427401 / 250000000000000000))) +
      6 * ((1388429763 / 1000000000000000000)) * ((83427401 / 250000000000000000)) * (126 / 100) + 8 * ((83427401 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13199 166) (d.f1 13199 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13199 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13199 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13199 166) (d.f1 13199 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13199 166) (d.w1 13199 166) (d.w2 13199 166)
  have hwexpr0 : 0 ≤ d.w0 13199 166 + d.w1 13199 166 * √(π / 2) +
      2 * d.w2 13199 166 + energyR16 13199 *
      radiusPolynomialRoot16 (d.w0 13199 166) (d.w1 13199 166) (d.w2 13199 166) := by
    positivity
  constructor
  · change (13199 : ℝ) ^ 8 * (mA 13199 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13199 166) (d.f1 13199 166) d.f2 + locationR16 13199 *
        radiusPolynomialRoot16 (d.f0 13199 166) (d.f1 13199 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13199 : ℝ) ^ 8 * (mA 13199 : ℝ) ^ 8 *
        ((((416174899 / 100000000000000000) : ℝ) ^ 2 + 2 * ((416174899 / 100000000000000000)) * ((1388429763 / 1000000000000000000)) * (126 / 100) +
          2 * (((1388429763 / 1000000000000000000)) ^ 2 + 2 * ((416174899 / 100000000000000000)) * ((83427401 / 250000000000000000))) +
          6 * ((1388429763 / 1000000000000000000)) * ((83427401 / 250000000000000000)) * (126 / 100) + 8 * ((83427401 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13199) *
          (32 * (((416174899 / 100000000000000000) : ℝ) + (1388429763 / 1000000000000000000) + (83427401 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13199 : ℝ) ^ 16 *
      (d.w0 13199 166 + d.w1 13199 166 * √(π / 2) + 2 * d.w2 13199 166 +
        energyR16 13199 * radiusPolynomialRoot16 (d.w0 13199 166) (d.w1 13199 166)
          (d.w2 13199 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13199 : ℝ) ^ 16 *
        (((163303379 / 10000000000000000000) : ℝ) + ((580936153 / 50000000000000000000)) * (126 / 100) + 2 * ((53064769 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13199) *
          (32 * (((163303379 / 10000000000000000000) : ℝ) + (580936153 / 50000000000000000000) + (53064769 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13199
