import BstLean.Part266Shard28Step4


/-! A coarse bound on the actual paper statistics constant at dimension 13050. -/
namespace BstLean.Part266.Row13050
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13048 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13048 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13048 128 ≤ (13302 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13302 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13050) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13050 : ℕ))
    (by norm_num : (13050 : ℕ) ≤ 16384)
  have ht : paperTail256 13050 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13050 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13050 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13050 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13050 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13050 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13048 128 * √(2 / (13050 : ℝ)) *
      (√(13050 : ℝ) + paperT0 13050 + paperTail256 13050) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13050 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13050 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13050 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13048 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13048 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13050 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13050

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13050
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13050 (61 / 100) 165 (17 / (100 * 13050)) (26 / (10 * 13050)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13050 (61 / 100) 165 (17 / (100 * 13050)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (43922277 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1346276709 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4112352273 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13050 / 13050 * (61 / 100)) ^ 4 * inverseRadius8 (13050 - 1) /
            envelopeGap 13050 (61 / 100) 165 (17 / (100 * 13050)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13050

namespace BstLean.Part266.Row13050
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13050 165 ≤ (2140784161 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13050 165 ≤ (714201793 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (171658667 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13050 165 ≤ (1689613851 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13050 165 ≤ (601063979 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13050 165 ≤ (219613377 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (43922277 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (43922277 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1346276709 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4112352273 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((902317 / 250000000) : ℝ) ≤ √(17 / (100 * 13050) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13050) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2095764229 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18345821793 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13050) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13050) ≤ (13546107 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13050) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13050 * (165 : ℝ) ^ 2 + 26 / (10 * 13050) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13050) : ℝ)) (tA 13050 * 165 ^ 2 + 26 / (10 * 13050)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((902317 / 250000000))) * ((43922277 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((902317 / 250000000)) ^ 3) * ((1346276709 / 1000000000000000000000000))) + ((4112352273 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((902317 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13050) : ℝ)) d.D d.V d.P (√(tA 13050) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((902317 / 250000000)) ^ 2 * (((2095764229 / 1000000000000000)) * ((18345821793 / 500000000000000000)))) + ((4112352273 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13050) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((902317 / 250000000)) * ((43922277 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13050) : ℝ)) (tA 13050 * 165 ^ 2 + 26 / (10 * 13050)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((43922277 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((902317 / 250000000)) ^ 2) * ((1346276709 / 1000000000000000000000000)) + ((4112352273 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13050) : ℝ)) (√(26 / (10 * 13050) : ℝ)) d.D d.V d.P (√(tA 13050) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((902317 / 250000000)) * (((2095764229 / 1000000000000000)) * ((18345821793 / 500000000000000000))) + ((4112352273 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13050) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((43922277 / 10000000000000000000) : ℝ) + ((4112352273 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13050

namespace BstLean.Part266.Row13050
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13050 165 ∧
    0 ≤ (tableEnvelope C).f1 13050 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13050 165 ∧
    0 ≤ (tableEnvelope C).w1 13050 165 ∧ 0 ≤ (tableEnvelope C).w2 13050 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13050 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13050 165 ∧ 0 ≤ d.f1 13050 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13050 165 ∧ 0 ≤ d.w1 13050 165 ∧ 0 ≤ d.w2 13050 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13050 ≤ 2 * (228 / 100 : ℝ) / 13050 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13050 ≤ 2 * (370 / 100 : ℝ) / 13050 := by
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
    (completeRAData (tableEnvelope C) 13050 165).locationBound 13050 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13050 165).energyBound 13050 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13050 165) (d.f1 13050 165) d.f2 ≤
      32 * (((2140784161 / 500000000000000000) : ℝ) + (714201793 / 500000000000000000) + (171658667 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13050 165) (d.w1 13050 165)
      (d.w2 13050 165) ≤
      32 * (((1689613851 / 100000000000000000000) : ℝ) + (601063979 / 50000000000000000000) + (219613377 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13050 165) (d.f1 13050 165) d.f2 ≤
      ((2140784161 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2140784161 / 500000000000000000)) * ((714201793 / 500000000000000000)) * (126 / 100) +
      2 * (((714201793 / 500000000000000000)) ^ 2 + 2 * ((2140784161 / 500000000000000000)) * ((171658667 / 500000000000000000))) +
      6 * ((714201793 / 500000000000000000)) * ((171658667 / 500000000000000000)) * (126 / 100) + 8 * ((171658667 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13050 165) (d.f1 13050 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13050 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13050 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13050 165) (d.f1 13050 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13050 165) (d.w1 13050 165) (d.w2 13050 165)
  have hwexpr0 : 0 ≤ d.w0 13050 165 + d.w1 13050 165 * √(π / 2) +
      2 * d.w2 13050 165 + energyR16 13050 *
      radiusPolynomialRoot16 (d.w0 13050 165) (d.w1 13050 165) (d.w2 13050 165) := by
    positivity
  constructor
  · change (13050 : ℝ) ^ 8 * (mA 13050 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13050 165) (d.f1 13050 165) d.f2 + locationR16 13050 *
        radiusPolynomialRoot16 (d.f0 13050 165) (d.f1 13050 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13050 : ℝ) ^ 8 * (mA 13050 : ℝ) ^ 8 *
        ((((2140784161 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2140784161 / 500000000000000000)) * ((714201793 / 500000000000000000)) * (126 / 100) +
          2 * (((714201793 / 500000000000000000)) ^ 2 + 2 * ((2140784161 / 500000000000000000)) * ((171658667 / 500000000000000000))) +
          6 * ((714201793 / 500000000000000000)) * ((171658667 / 500000000000000000)) * (126 / 100) + 8 * ((171658667 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13050) *
          (32 * (((2140784161 / 500000000000000000) : ℝ) + (714201793 / 500000000000000000) + (171658667 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13050 : ℝ) ^ 16 *
      (d.w0 13050 165 + d.w1 13050 165 * √(π / 2) + 2 * d.w2 13050 165 +
        energyR16 13050 * radiusPolynomialRoot16 (d.w0 13050 165) (d.w1 13050 165)
          (d.w2 13050 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13050 : ℝ) ^ 16 *
        (((1689613851 / 100000000000000000000) : ℝ) + ((601063979 / 50000000000000000000)) * (126 / 100) + 2 * ((219613377 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13050) *
          (32 * (((1689613851 / 100000000000000000000) : ℝ) + (601063979 / 50000000000000000000) + (219613377 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13050

/-! A coarse bound on the actual paper statistics constant at dimension 13051. -/
namespace BstLean.Part266.Row13051
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13049 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13049 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13049 128 ≤ (13303 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13303 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13051) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13051 : ℕ))
    (by norm_num : (13051 : ℕ) ≤ 16384)
  have ht : paperTail256 13051 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13051 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13051 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13051 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13051 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13051 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13049 128 * √(2 / (13051 : ℝ)) *
      (√(13051 : ℝ) + paperT0 13051 + paperTail256 13051) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13051 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13051 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13051 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13049 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13049 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13051 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13051

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13051
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13051 (61 / 100) 165 (17 / (100 * 13051)) (26 / (10 * 13051)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13051 (61 / 100) 165 (17 / (100 * 13051)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (43912181 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (33646603 / 25000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1027452087 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13051 / 13051 * (61 / 100)) ^ 4 * inverseRadius8 (13051 - 1) /
            envelopeGap 13051 (61 / 100) 165 (17 / (100 * 13051)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13051

namespace BstLean.Part266.Row13051
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13051 165 ≤ (1070186801 / 250000000000000000)
  f1 : (tableEnvelope C).f1 13051 165 ≤ (285625949 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (343251543 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13051 165 ≤ (1689225281 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13051 165 ≤ (1201851543 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13051 165 ≤ (13722681 / 3125000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (43912181 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (43912181 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (33646603 / 25000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1027452087 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((360913 / 100000000) : ℝ) ≤ √(17 / (100 * 13051) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13051) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (523880837 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36686020771 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13051) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13051) ≤ (13545069 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13051) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13051 * (165 : ℝ) ^ 2 + 26 / (10 * 13051) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13051) : ℝ)) (tA 13051 * 165 ^ 2 + 26 / (10 * 13051)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((360913 / 100000000))) * ((43912181 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((360913 / 100000000)) ^ 3) * ((33646603 / 25000000000000000000000))) + ((1027452087 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((360913 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13051) : ℝ)) d.D d.V d.P (√(tA 13051) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((360913 / 100000000)) ^ 2 * (((523880837 / 250000000000000)) * ((36686020771 / 1000000000000000000)))) + ((1027452087 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13051) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((360913 / 100000000)) * ((43912181 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13051) : ℝ)) (tA 13051 * 165 ^ 2 + 26 / (10 * 13051)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((43912181 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((360913 / 100000000)) ^ 2) * ((33646603 / 25000000000000000000000)) + ((1027452087 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13051) : ℝ)) (√(26 / (10 * 13051) : ℝ)) d.D d.V d.P (√(tA 13051) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((360913 / 100000000)) * (((523880837 / 250000000000000)) * ((36686020771 / 1000000000000000000))) + ((1027452087 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13051) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((43912181 / 10000000000000000000) : ℝ) + ((1027452087 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13051

namespace BstLean.Part266.Row13051
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13051 165 ∧
    0 ≤ (tableEnvelope C).f1 13051 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13051 165 ∧
    0 ≤ (tableEnvelope C).w1 13051 165 ∧ 0 ≤ (tableEnvelope C).w2 13051 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13051 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13051 165 ∧ 0 ≤ d.f1 13051 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13051 165 ∧ 0 ≤ d.w1 13051 165 ∧ 0 ≤ d.w2 13051 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13051 ≤ 2 * (228 / 100 : ℝ) / 13051 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13051 ≤ 2 * (370 / 100 : ℝ) / 13051 := by
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
    (completeRAData (tableEnvelope C) 13051 165).locationBound 13051 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13051 165).energyBound 13051 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13051 165) (d.f1 13051 165) d.f2 ≤
      32 * (((1070186801 / 250000000000000000) : ℝ) + (285625949 / 200000000000000000) + (343251543 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13051 165) (d.w1 13051 165)
      (d.w2 13051 165) ≤
      32 * (((1689225281 / 100000000000000000000) : ℝ) + (1201851543 / 100000000000000000000) + (13722681 / 3125000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13051 165) (d.f1 13051 165) d.f2 ≤
      ((1070186801 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1070186801 / 250000000000000000)) * ((285625949 / 200000000000000000)) * (126 / 100) +
      2 * (((285625949 / 200000000000000000)) ^ 2 + 2 * ((1070186801 / 250000000000000000)) * ((343251543 / 1000000000000000000))) +
      6 * ((285625949 / 200000000000000000)) * ((343251543 / 1000000000000000000)) * (126 / 100) + 8 * ((343251543 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13051 165) (d.f1 13051 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13051 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13051 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13051 165) (d.f1 13051 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13051 165) (d.w1 13051 165) (d.w2 13051 165)
  have hwexpr0 : 0 ≤ d.w0 13051 165 + d.w1 13051 165 * √(π / 2) +
      2 * d.w2 13051 165 + energyR16 13051 *
      radiusPolynomialRoot16 (d.w0 13051 165) (d.w1 13051 165) (d.w2 13051 165) := by
    positivity
  constructor
  · change (13051 : ℝ) ^ 8 * (mA 13051 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13051 165) (d.f1 13051 165) d.f2 + locationR16 13051 *
        radiusPolynomialRoot16 (d.f0 13051 165) (d.f1 13051 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13051 : ℝ) ^ 8 * (mA 13051 : ℝ) ^ 8 *
        ((((1070186801 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1070186801 / 250000000000000000)) * ((285625949 / 200000000000000000)) * (126 / 100) +
          2 * (((285625949 / 200000000000000000)) ^ 2 + 2 * ((1070186801 / 250000000000000000)) * ((343251543 / 1000000000000000000))) +
          6 * ((285625949 / 200000000000000000)) * ((343251543 / 1000000000000000000)) * (126 / 100) + 8 * ((343251543 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13051) *
          (32 * (((1070186801 / 250000000000000000) : ℝ) + (285625949 / 200000000000000000) + (343251543 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13051 : ℝ) ^ 16 *
      (d.w0 13051 165 + d.w1 13051 165 * √(π / 2) + 2 * d.w2 13051 165 +
        energyR16 13051 * radiusPolynomialRoot16 (d.w0 13051 165) (d.w1 13051 165)
          (d.w2 13051 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13051 : ℝ) ^ 16 *
        (((1689225281 / 100000000000000000000) : ℝ) + ((1201851543 / 100000000000000000000)) * (126 / 100) + 2 * ((13722681 / 3125000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13051) *
          (32 * (((1689225281 / 100000000000000000000) : ℝ) + (1201851543 / 100000000000000000000) + (13722681 / 3125000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13051

/-! A coarse bound on the actual paper statistics constant at dimension 13052. -/
namespace BstLean.Part266.Row13052
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13050 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13050 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13050 128 ≤ (13304 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13304 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13052) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13052 : ℕ))
    (by norm_num : (13052 : ℕ) ≤ 16384)
  have ht : paperTail256 13052 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13052 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13052 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13052 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13052 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13052 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13050 128 * √(2 / (13052 : ℝ)) *
      (√(13052 : ℝ) + paperT0 13052 + paperTail256 13052) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13052 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13052 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13052 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13050 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13050 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13052 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13052

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13052
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13052 (61 / 100) 165 (17 / (100 * 13052)) (26 / (10 * 13052)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13052 (61 / 100) 165 (17 / (100 * 13052)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (5487761 / 1250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1345451689 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2053633097 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13052 / 13052 * (61 / 100)) ^ 4 * inverseRadius8 (13052 - 1) /
            envelopeGap 13052 (61 / 100) 165 (17 / (100 * 13052)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13052

namespace BstLean.Part266.Row13052
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13052 165 ≤ (4279926361 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13052 165 ≤ (1427855989 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (34318577 / 100000000000000000)
  w0 : (tableEnvelope C).w0 13052 165 ≤ (1688836839 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13052 165 ≤ (75098451 / 6250000000000000000)
  w2 : (tableEnvelope C).w2 13052 165 ≤ (439024859 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (5487761 / 1250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (5487761 / 1250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1345451689 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2053633097 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((112781 / 31250000) : ℝ) ≤ √(17 / (100 * 13052) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13052) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2095282511 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36680399249 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13052) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13052) ≤ (433409 / 4000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13052) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13052 * (165 : ℝ) ^ 2 + 26 / (10 * 13052) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13052) : ℝ)) (tA 13052 * 165 ^ 2 + 26 / (10 * 13052)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((112781 / 31250000))) * ((5487761 / 1250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((112781 / 31250000)) ^ 3) * ((1345451689 / 1000000000000000000000000))) + ((2053633097 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((112781 / 31250000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13052) : ℝ)) d.D d.V d.P (√(tA 13052) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((112781 / 31250000)) ^ 2 * (((2095282511 / 1000000000000000)) * ((36680399249 / 1000000000000000000)))) + ((2053633097 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13052) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((112781 / 31250000)) * ((5487761 / 1250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13052) : ℝ)) (tA 13052 * 165 ^ 2 + 26 / (10 * 13052)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((5487761 / 1250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((112781 / 31250000)) ^ 2) * ((1345451689 / 1000000000000000000000000)) + ((2053633097 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13052) : ℝ)) (√(26 / (10 * 13052) : ℝ)) d.D d.V d.P (√(tA 13052) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((112781 / 31250000)) * (((2095282511 / 1000000000000000)) * ((36680399249 / 1000000000000000000))) + ((2053633097 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13052) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((5487761 / 1250000000000000000) : ℝ) + ((2053633097 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13052

namespace BstLean.Part266.Row13052
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13052 165 ∧
    0 ≤ (tableEnvelope C).f1 13052 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13052 165 ∧
    0 ≤ (tableEnvelope C).w1 13052 165 ∧ 0 ≤ (tableEnvelope C).w2 13052 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13052 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13052 165 ∧ 0 ≤ d.f1 13052 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13052 165 ∧ 0 ≤ d.w1 13052 165 ∧ 0 ≤ d.w2 13052 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13052 ≤ 2 * (228 / 100 : ℝ) / 13052 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13052 ≤ 2 * (370 / 100 : ℝ) / 13052 := by
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
    (completeRAData (tableEnvelope C) 13052 165).locationBound 13052 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13052 165).energyBound 13052 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13052 165) (d.f1 13052 165) d.f2 ≤
      32 * (((4279926361 / 1000000000000000000) : ℝ) + (1427855989 / 1000000000000000000) + (34318577 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13052 165) (d.w1 13052 165)
      (d.w2 13052 165) ≤
      32 * (((1688836839 / 100000000000000000000) : ℝ) + (75098451 / 6250000000000000000) + (439024859 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13052 165) (d.f1 13052 165) d.f2 ≤
      ((4279926361 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4279926361 / 1000000000000000000)) * ((1427855989 / 1000000000000000000)) * (126 / 100) +
      2 * (((1427855989 / 1000000000000000000)) ^ 2 + 2 * ((4279926361 / 1000000000000000000)) * ((34318577 / 100000000000000000))) +
      6 * ((1427855989 / 1000000000000000000)) * ((34318577 / 100000000000000000)) * (126 / 100) + 8 * ((34318577 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13052 165) (d.f1 13052 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13052 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13052 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13052 165) (d.f1 13052 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13052 165) (d.w1 13052 165) (d.w2 13052 165)
  have hwexpr0 : 0 ≤ d.w0 13052 165 + d.w1 13052 165 * √(π / 2) +
      2 * d.w2 13052 165 + energyR16 13052 *
      radiusPolynomialRoot16 (d.w0 13052 165) (d.w1 13052 165) (d.w2 13052 165) := by
    positivity
  constructor
  · change (13052 : ℝ) ^ 8 * (mA 13052 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13052 165) (d.f1 13052 165) d.f2 + locationR16 13052 *
        radiusPolynomialRoot16 (d.f0 13052 165) (d.f1 13052 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13052 : ℝ) ^ 8 * (mA 13052 : ℝ) ^ 8 *
        ((((4279926361 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4279926361 / 1000000000000000000)) * ((1427855989 / 1000000000000000000)) * (126 / 100) +
          2 * (((1427855989 / 1000000000000000000)) ^ 2 + 2 * ((4279926361 / 1000000000000000000)) * ((34318577 / 100000000000000000))) +
          6 * ((1427855989 / 1000000000000000000)) * ((34318577 / 100000000000000000)) * (126 / 100) + 8 * ((34318577 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13052) *
          (32 * (((4279926361 / 1000000000000000000) : ℝ) + (1427855989 / 1000000000000000000) + (34318577 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13052 : ℝ) ^ 16 *
      (d.w0 13052 165 + d.w1 13052 165 * √(π / 2) + 2 * d.w2 13052 165 +
        energyR16 13052 * radiusPolynomialRoot16 (d.w0 13052 165) (d.w1 13052 165)
          (d.w2 13052 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13052 : ℝ) ^ 16 *
        (((1688836839 / 100000000000000000000) : ℝ) + ((75098451 / 6250000000000000000)) * (126 / 100) + 2 * ((439024859 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13052) *
          (32 * (((1688836839 / 100000000000000000000) : ℝ) + (75098451 / 6250000000000000000) + (439024859 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13052

/-! A coarse bound on the actual paper statistics constant at dimension 13053. -/
namespace BstLean.Part266.Row13053
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13051 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13051 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13051 128 ≤ (13305 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13305 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13053) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13053 : ℕ))
    (by norm_num : (13053 : ℕ) ≤ 16384)
  have ht : paperTail256 13053 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13053 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13053 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13053 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13053 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13053 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13051 128 * √(2 / (13053 : ℝ)) *
      (√(13053 : ℝ) + paperT0 13053 + paperTail256 13053) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13053 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13053 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13053 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13051 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13051 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13053 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13053

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13053
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13053 (61 / 100) 165 (17 / (100 * 13053)) (26 / (10 * 13053)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13053 (61 / 100) 165 (17 / (100 * 13053)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (219459991 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1345039417 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1026181453 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13053 / 13053 * (61 / 100)) ^ 4 * inverseRadius8 (13053 - 1) /
            envelopeGap 13053 (61 / 100) 165 (17 / (100 * 13053)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13053

namespace BstLean.Part266.Row13053
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13053 165 ≤ (2139554609 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13053 165 ≤ (178447889 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (343120113 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13053 165 ≤ (1688449223 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13053 165 ≤ (600649657 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13053 165 ≤ (438923959 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (219459991 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (219459991 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1345039417 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1026181453 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3608853 / 1000000000) : ℝ) ≤ √(17 / (100 * 13053) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13053) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2095041723 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4584347379 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13053) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13053) ≤ (108343949 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13053) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13053 * (165 : ℝ) ^ 2 + 26 / (10 * 13053) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13053) : ℝ)) (tA 13053 * 165 ^ 2 + 26 / (10 * 13053)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3608853 / 1000000000))) * ((219459991 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3608853 / 1000000000)) ^ 3) * ((1345039417 / 1000000000000000000000000))) + ((1026181453 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3608853 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13053) : ℝ)) d.D d.V d.P (√(tA 13053) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3608853 / 1000000000)) ^ 2 * (((2095041723 / 1000000000000000)) * ((4584347379 / 125000000000000000)))) + ((1026181453 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13053) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3608853 / 1000000000)) * ((219459991 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13053) : ℝ)) (tA 13053 * 165 ^ 2 + 26 / (10 * 13053)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((219459991 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3608853 / 1000000000)) ^ 2) * ((1345039417 / 1000000000000000000000000)) + ((1026181453 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13053) : ℝ)) (√(26 / (10 * 13053) : ℝ)) d.D d.V d.P (√(tA 13053) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3608853 / 1000000000)) * (((2095041723 / 1000000000000000)) * ((4584347379 / 125000000000000000))) + ((1026181453 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13053) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((219459991 / 50000000000000000000) : ℝ) + ((1026181453 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13053

namespace BstLean.Part266.Row13053
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13053 165 ∧
    0 ≤ (tableEnvelope C).f1 13053 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13053 165 ∧
    0 ≤ (tableEnvelope C).w1 13053 165 ∧ 0 ≤ (tableEnvelope C).w2 13053 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13053 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13053 165 ∧ 0 ≤ d.f1 13053 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13053 165 ∧ 0 ≤ d.w1 13053 165 ∧ 0 ≤ d.w2 13053 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13053 ≤ 2 * (228 / 100 : ℝ) / 13053 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13053 ≤ 2 * (370 / 100 : ℝ) / 13053 := by
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
    (completeRAData (tableEnvelope C) 13053 165).locationBound 13053 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13053 165).energyBound 13053 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13053 165) (d.f1 13053 165) d.f2 ≤
      32 * (((2139554609 / 500000000000000000) : ℝ) + (178447889 / 125000000000000000) + (343120113 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13053 165) (d.w1 13053 165)
      (d.w2 13053 165) ≤
      32 * (((1688449223 / 100000000000000000000) : ℝ) + (600649657 / 50000000000000000000) + (438923959 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13053 165) (d.f1 13053 165) d.f2 ≤
      ((2139554609 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2139554609 / 500000000000000000)) * ((178447889 / 125000000000000000)) * (126 / 100) +
      2 * (((178447889 / 125000000000000000)) ^ 2 + 2 * ((2139554609 / 500000000000000000)) * ((343120113 / 1000000000000000000))) +
      6 * ((178447889 / 125000000000000000)) * ((343120113 / 1000000000000000000)) * (126 / 100) + 8 * ((343120113 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13053 165) (d.f1 13053 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13053 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13053 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13053 165) (d.f1 13053 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13053 165) (d.w1 13053 165) (d.w2 13053 165)
  have hwexpr0 : 0 ≤ d.w0 13053 165 + d.w1 13053 165 * √(π / 2) +
      2 * d.w2 13053 165 + energyR16 13053 *
      radiusPolynomialRoot16 (d.w0 13053 165) (d.w1 13053 165) (d.w2 13053 165) := by
    positivity
  constructor
  · change (13053 : ℝ) ^ 8 * (mA 13053 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13053 165) (d.f1 13053 165) d.f2 + locationR16 13053 *
        radiusPolynomialRoot16 (d.f0 13053 165) (d.f1 13053 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13053 : ℝ) ^ 8 * (mA 13053 : ℝ) ^ 8 *
        ((((2139554609 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2139554609 / 500000000000000000)) * ((178447889 / 125000000000000000)) * (126 / 100) +
          2 * (((178447889 / 125000000000000000)) ^ 2 + 2 * ((2139554609 / 500000000000000000)) * ((343120113 / 1000000000000000000))) +
          6 * ((178447889 / 125000000000000000)) * ((343120113 / 1000000000000000000)) * (126 / 100) + 8 * ((343120113 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13053) *
          (32 * (((2139554609 / 500000000000000000) : ℝ) + (178447889 / 125000000000000000) + (343120113 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13053 : ℝ) ^ 16 *
      (d.w0 13053 165 + d.w1 13053 165 * √(π / 2) + 2 * d.w2 13053 165 +
        energyR16 13053 * radiusPolynomialRoot16 (d.w0 13053 165) (d.w1 13053 165)
          (d.w2 13053 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13053 : ℝ) ^ 16 *
        (((1688449223 / 100000000000000000000) : ℝ) + ((600649657 / 50000000000000000000)) * (126 / 100) + 2 * ((438923959 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13053) *
          (32 * (((1688449223 / 100000000000000000000) : ℝ) + (600649657 / 50000000000000000000) + (438923959 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13053

/-! A coarse bound on the actual paper statistics constant at dimension 13054. -/
namespace BstLean.Part266.Row13054
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13052 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13052 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13052 128 ≤ (13306 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13306 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13054) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13054 : ℕ))
    (by norm_num : (13054 : ℕ) ≤ 16384)
  have ht : paperTail256 13054 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13054 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13054 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13054 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13054 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13054 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13052 128 * √(2 / (13054 : ℝ)) *
      (√(13054 : ℝ) + paperT0 13054 + paperTail256 13054) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13054 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13054 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13054 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13052 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13052 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13054 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13054

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13054
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13054 (61 / 100) 165 (17 / (100 * 13054)) (26 / (10 * 13054)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13054 (61 / 100) 165 (17 / (100 * 13054)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (219409557 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (672313651 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4102187199 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13054 / 13054 * (61 / 100)) ^ 4 * inverseRadius8 (13054 - 1) /
            envelopeGap 13054 (61 / 100) 165 (17 / (100 * 13054)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13054

namespace BstLean.Part266.Row13054
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13054 165 ≤ (4278288923 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13054 165 ≤ (178413691 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (343054379 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13054 165 ≤ (844030521 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13054 165 ≤ (1201023167 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13054 165 ≤ (27426443 / 6250000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (219409557 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (219409557 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (672313651 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4102187199 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((721743 / 200000000) : ℝ) ≤ √(17 / (100 * 13054) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13054) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2094800979 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7333832019 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13054) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13054) ≤ (2166713 / 20000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13054) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13054 * (165 : ℝ) ^ 2 + 26 / (10 * 13054) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13054) : ℝ)) (tA 13054 * 165 ^ 2 + 26 / (10 * 13054)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((721743 / 200000000))) * ((219409557 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((721743 / 200000000)) ^ 3) * ((672313651 / 500000000000000000000000))) + ((4102187199 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((721743 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13054) : ℝ)) d.D d.V d.P (√(tA 13054) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((721743 / 200000000)) ^ 2 * (((2094800979 / 1000000000000000)) * ((7333832019 / 200000000000000000)))) + ((4102187199 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13054) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((721743 / 200000000)) * ((219409557 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13054) : ℝ)) (tA 13054 * 165 ^ 2 + 26 / (10 * 13054)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((219409557 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((721743 / 200000000)) ^ 2) * ((672313651 / 500000000000000000000000)) + ((4102187199 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13054) : ℝ)) (√(26 / (10 * 13054) : ℝ)) d.D d.V d.P (√(tA 13054) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((721743 / 200000000)) * (((2094800979 / 1000000000000000)) * ((7333832019 / 200000000000000000))) + ((4102187199 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13054) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((219409557 / 50000000000000000000) : ℝ) + ((4102187199 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13054

namespace BstLean.Part266.Row13054
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13054 165 ∧
    0 ≤ (tableEnvelope C).f1 13054 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13054 165 ∧
    0 ≤ (tableEnvelope C).w1 13054 165 ∧ 0 ≤ (tableEnvelope C).w2 13054 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13054 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13054 165 ∧ 0 ≤ d.f1 13054 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13054 165 ∧ 0 ≤ d.w1 13054 165 ∧ 0 ≤ d.w2 13054 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13054 ≤ 2 * (228 / 100 : ℝ) / 13054 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13054 ≤ 2 * (370 / 100 : ℝ) / 13054 := by
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
    (completeRAData (tableEnvelope C) 13054 165).locationBound 13054 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13054 165).energyBound 13054 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13054 165) (d.f1 13054 165) d.f2 ≤
      32 * (((4278288923 / 1000000000000000000) : ℝ) + (178413691 / 125000000000000000) + (343054379 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13054 165) (d.w1 13054 165)
      (d.w2 13054 165) ≤
      32 * (((844030521 / 50000000000000000000) : ℝ) + (1201023167 / 100000000000000000000) + (27426443 / 6250000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13054 165) (d.f1 13054 165) d.f2 ≤
      ((4278288923 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4278288923 / 1000000000000000000)) * ((178413691 / 125000000000000000)) * (126 / 100) +
      2 * (((178413691 / 125000000000000000)) ^ 2 + 2 * ((4278288923 / 1000000000000000000)) * ((343054379 / 1000000000000000000))) +
      6 * ((178413691 / 125000000000000000)) * ((343054379 / 1000000000000000000)) * (126 / 100) + 8 * ((343054379 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13054 165) (d.f1 13054 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13054 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13054 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13054 165) (d.f1 13054 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13054 165) (d.w1 13054 165) (d.w2 13054 165)
  have hwexpr0 : 0 ≤ d.w0 13054 165 + d.w1 13054 165 * √(π / 2) +
      2 * d.w2 13054 165 + energyR16 13054 *
      radiusPolynomialRoot16 (d.w0 13054 165) (d.w1 13054 165) (d.w2 13054 165) := by
    positivity
  constructor
  · change (13054 : ℝ) ^ 8 * (mA 13054 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13054 165) (d.f1 13054 165) d.f2 + locationR16 13054 *
        radiusPolynomialRoot16 (d.f0 13054 165) (d.f1 13054 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13054 : ℝ) ^ 8 * (mA 13054 : ℝ) ^ 8 *
        ((((4278288923 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4278288923 / 1000000000000000000)) * ((178413691 / 125000000000000000)) * (126 / 100) +
          2 * (((178413691 / 125000000000000000)) ^ 2 + 2 * ((4278288923 / 1000000000000000000)) * ((343054379 / 1000000000000000000))) +
          6 * ((178413691 / 125000000000000000)) * ((343054379 / 1000000000000000000)) * (126 / 100) + 8 * ((343054379 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13054) *
          (32 * (((4278288923 / 1000000000000000000) : ℝ) + (178413691 / 125000000000000000) + (343054379 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13054 : ℝ) ^ 16 *
      (d.w0 13054 165 + d.w1 13054 165 * √(π / 2) + 2 * d.w2 13054 165 +
        energyR16 13054 * radiusPolynomialRoot16 (d.w0 13054 165) (d.w1 13054 165)
          (d.w2 13054 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13054 : ℝ) ^ 16 *
        (((844030521 / 50000000000000000000) : ℝ) + ((1201023167 / 100000000000000000000)) * (126 / 100) + 2 * ((27426443 / 6250000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13054) *
          (32 * (((844030521 / 50000000000000000000) : ℝ) + (1201023167 / 100000000000000000000) + (27426443 / 6250000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13054

/-! A coarse bound on the actual paper statistics constant at dimension 13055. -/
namespace BstLean.Part266.Row13055
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13053 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13053 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13053 128 ≤ (13307 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13307 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13055) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13055 : ℕ))
    (by norm_num : (13055 : ℕ) ≤ 16384)
  have ht : paperTail256 13055 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13055 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13055 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13055 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13055 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13055 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13053 128 * √(2 / (13055 : ℝ)) *
      (√(13055 : ℝ) + paperT0 13055 + paperTail256 13055) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13055 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13055 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13055 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13053 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13053 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13055 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13055

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13055
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13055 (61 / 100) 165 (17 / (100 * 13055)) (26 / (10 * 13055)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13055 (61 / 100) 165 (17 / (100 * 13055)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (438718277 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (268843069 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4099650353 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13055 / 13055 * (61 / 100)) ^ 4 * inverseRadius8 (13055 - 1) /
            envelopeGap 13055 (61 / 100) 165 (17 / (100 * 13055)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13055

namespace BstLean.Part266.Row13055
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13055 165 ≤ (534683613 / 125000000000000000)
  f1 : (tableEnvelope C).f1 13055 165 ≤ (1427036031 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (42873583 / 125000000000000000)
  w0 : (tableEnvelope C).w0 13055 165 ≤ (1687672991 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13055 165 ≤ (1200747111 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13055 165 ≤ (438722249 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (438718277 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (438718277 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (268843069 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4099650353 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3608577 / 1000000000) : ℝ) ≤ √(17 / (100 * 13055) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13055) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2094560281 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36663542451 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13055) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13055) ≤ (108327351 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13055) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13055 * (165 : ℝ) ^ 2 + 26 / (10 * 13055) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13055) : ℝ)) (tA 13055 * 165 ^ 2 + 26 / (10 * 13055)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3608577 / 1000000000))) * ((438718277 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3608577 / 1000000000)) ^ 3) * ((268843069 / 200000000000000000000000))) + ((4099650353 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3608577 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13055) : ℝ)) d.D d.V d.P (√(tA 13055) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3608577 / 1000000000)) ^ 2 * (((2094560281 / 1000000000000000)) * ((36663542451 / 1000000000000000000)))) + ((4099650353 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13055) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3608577 / 1000000000)) * ((438718277 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13055) : ℝ)) (tA 13055 * 165 ^ 2 + 26 / (10 * 13055)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((438718277 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3608577 / 1000000000)) ^ 2) * ((268843069 / 200000000000000000000000)) + ((4099650353 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13055) : ℝ)) (√(26 / (10 * 13055) : ℝ)) d.D d.V d.P (√(tA 13055) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3608577 / 1000000000)) * (((2094560281 / 1000000000000000)) * ((36663542451 / 1000000000000000000))) + ((4099650353 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13055) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((438718277 / 100000000000000000000) : ℝ) + ((4099650353 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13055

namespace BstLean.Part266.Row13055
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13055 165 ∧
    0 ≤ (tableEnvelope C).f1 13055 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13055 165 ∧
    0 ≤ (tableEnvelope C).w1 13055 165 ∧ 0 ≤ (tableEnvelope C).w2 13055 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13055 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13055 165 ∧ 0 ≤ d.f1 13055 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13055 165 ∧ 0 ≤ d.w1 13055 165 ∧ 0 ≤ d.w2 13055 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13055 ≤ 2 * (228 / 100 : ℝ) / 13055 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13055 ≤ 2 * (370 / 100 : ℝ) / 13055 := by
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
    (completeRAData (tableEnvelope C) 13055 165).locationBound 13055 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13055 165).energyBound 13055 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13055 165) (d.f1 13055 165) d.f2 ≤
      32 * (((534683613 / 125000000000000000) : ℝ) + (1427036031 / 1000000000000000000) + (42873583 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13055 165) (d.w1 13055 165)
      (d.w2 13055 165) ≤
      32 * (((1687672991 / 100000000000000000000) : ℝ) + (1200747111 / 100000000000000000000) + (438722249 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13055 165) (d.f1 13055 165) d.f2 ≤
      ((534683613 / 125000000000000000) : ℝ) ^ 2 + 2 * ((534683613 / 125000000000000000)) * ((1427036031 / 1000000000000000000)) * (126 / 100) +
      2 * (((1427036031 / 1000000000000000000)) ^ 2 + 2 * ((534683613 / 125000000000000000)) * ((42873583 / 125000000000000000))) +
      6 * ((1427036031 / 1000000000000000000)) * ((42873583 / 125000000000000000)) * (126 / 100) + 8 * ((42873583 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13055 165) (d.f1 13055 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13055 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13055 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13055 165) (d.f1 13055 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13055 165) (d.w1 13055 165) (d.w2 13055 165)
  have hwexpr0 : 0 ≤ d.w0 13055 165 + d.w1 13055 165 * √(π / 2) +
      2 * d.w2 13055 165 + energyR16 13055 *
      radiusPolynomialRoot16 (d.w0 13055 165) (d.w1 13055 165) (d.w2 13055 165) := by
    positivity
  constructor
  · change (13055 : ℝ) ^ 8 * (mA 13055 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13055 165) (d.f1 13055 165) d.f2 + locationR16 13055 *
        radiusPolynomialRoot16 (d.f0 13055 165) (d.f1 13055 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13055 : ℝ) ^ 8 * (mA 13055 : ℝ) ^ 8 *
        ((((534683613 / 125000000000000000) : ℝ) ^ 2 + 2 * ((534683613 / 125000000000000000)) * ((1427036031 / 1000000000000000000)) * (126 / 100) +
          2 * (((1427036031 / 1000000000000000000)) ^ 2 + 2 * ((534683613 / 125000000000000000)) * ((42873583 / 125000000000000000))) +
          6 * ((1427036031 / 1000000000000000000)) * ((42873583 / 125000000000000000)) * (126 / 100) + 8 * ((42873583 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13055) *
          (32 * (((534683613 / 125000000000000000) : ℝ) + (1427036031 / 1000000000000000000) + (42873583 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13055 : ℝ) ^ 16 *
      (d.w0 13055 165 + d.w1 13055 165 * √(π / 2) + 2 * d.w2 13055 165 +
        energyR16 13055 * radiusPolynomialRoot16 (d.w0 13055 165) (d.w1 13055 165)
          (d.w2 13055 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13055 : ℝ) ^ 16 *
        (((1687672991 / 100000000000000000000) : ℝ) + ((1200747111 / 100000000000000000000)) * (126 / 100) + 2 * ((438722249 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13055) *
          (32 * (((1687672991 / 100000000000000000000) : ℝ) + (1200747111 / 100000000000000000000) + (438722249 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13055

/-! A coarse bound on the actual paper statistics constant at dimension 13056. -/
namespace BstLean.Part266.Row13056
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13054 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13054 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13054 128 ≤ (13308 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13308 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13056) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13056 : ℕ))
    (by norm_num : (13056 : ℕ) ≤ 16384)
  have ht : paperTail256 13056 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13056 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13056 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13056 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13056 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13056 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13054 128 * √(2 / (13056 : ℝ)) *
      (√(13056 : ℝ) + paperT0 13056 + paperTail256 13056) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13056 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13056 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13056 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13054 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13054 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13056 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13056

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13056
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13056 (61 / 100) 165 (17 / (100 * 13056)) (26 / (10 * 13056)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13056 (61 / 100) 165 (17 / (100 * 13056)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (438617471 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (671901773 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (163884611 / 40000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13056 / 13056 * (61 / 100)) ^ 4 * inverseRadius8 (13056 - 1) /
            envelopeGap 13056 (61 / 100) 165 (17 / (100 * 13056)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13056

namespace BstLean.Part266.Row13056
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13056 165 ≤ (4276649159 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13056 165 ≤ (1426762619 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (42865371 / 125000000000000000)
  w0 : (tableEnvelope C).w0 13056 165 ≤ (1687285071 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13056 165 ≤ (150058893 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 13056 165 ≤ (342673 / 78125000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (438617471 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (438617471 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (671901773 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (163884611 / 40000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3608439 / 1000000000) : ℝ) ≤ √(17 / (100 * 13056) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13056) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (209431963 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36657926101 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13056) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13056) ≤ (54159527 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13056) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13056 * (165 : ℝ) ^ 2 + 26 / (10 * 13056) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13056) : ℝ)) (tA 13056 * 165 ^ 2 + 26 / (10 * 13056)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3608439 / 1000000000))) * ((438617471 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3608439 / 1000000000)) ^ 3) * ((671901773 / 500000000000000000000000))) + ((163884611 / 40000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3608439 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13056) : ℝ)) d.D d.V d.P (√(tA 13056) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3608439 / 1000000000)) ^ 2 * (((209431963 / 100000000000000)) * ((36657926101 / 1000000000000000000)))) + ((163884611 / 40000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13056) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3608439 / 1000000000)) * ((438617471 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13056) : ℝ)) (tA 13056 * 165 ^ 2 + 26 / (10 * 13056)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((438617471 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3608439 / 1000000000)) ^ 2) * ((671901773 / 500000000000000000000000)) + ((163884611 / 40000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13056) : ℝ)) (√(26 / (10 * 13056) : ℝ)) d.D d.V d.P (√(tA 13056) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3608439 / 1000000000)) * (((209431963 / 100000000000000)) * ((36657926101 / 1000000000000000000))) + ((163884611 / 40000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13056) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((438617471 / 100000000000000000000) : ℝ) + ((163884611 / 40000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13056

namespace BstLean.Part266.Row13056
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13056 165 ∧
    0 ≤ (tableEnvelope C).f1 13056 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13056 165 ∧
    0 ≤ (tableEnvelope C).w1 13056 165 ∧ 0 ≤ (tableEnvelope C).w2 13056 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13056 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13056 165 ∧ 0 ≤ d.f1 13056 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13056 165 ∧ 0 ≤ d.w1 13056 165 ∧ 0 ≤ d.w2 13056 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13056 ≤ 2 * (228 / 100 : ℝ) / 13056 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13056 ≤ 2 * (370 / 100 : ℝ) / 13056 := by
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
    (completeRAData (tableEnvelope C) 13056 165).locationBound 13056 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13056 165).energyBound 13056 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13056 165) (d.f1 13056 165) d.f2 ≤
      32 * (((4276649159 / 1000000000000000000) : ℝ) + (1426762619 / 1000000000000000000) + (42865371 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13056 165) (d.w1 13056 165)
      (d.w2 13056 165) ≤
      32 * (((1687285071 / 100000000000000000000) : ℝ) + (150058893 / 12500000000000000000) + (342673 / 78125000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13056 165) (d.f1 13056 165) d.f2 ≤
      ((4276649159 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4276649159 / 1000000000000000000)) * ((1426762619 / 1000000000000000000)) * (126 / 100) +
      2 * (((1426762619 / 1000000000000000000)) ^ 2 + 2 * ((4276649159 / 1000000000000000000)) * ((42865371 / 125000000000000000))) +
      6 * ((1426762619 / 1000000000000000000)) * ((42865371 / 125000000000000000)) * (126 / 100) + 8 * ((42865371 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13056 165) (d.f1 13056 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13056 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13056 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13056 165) (d.f1 13056 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13056 165) (d.w1 13056 165) (d.w2 13056 165)
  have hwexpr0 : 0 ≤ d.w0 13056 165 + d.w1 13056 165 * √(π / 2) +
      2 * d.w2 13056 165 + energyR16 13056 *
      radiusPolynomialRoot16 (d.w0 13056 165) (d.w1 13056 165) (d.w2 13056 165) := by
    positivity
  constructor
  · change (13056 : ℝ) ^ 8 * (mA 13056 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13056 165) (d.f1 13056 165) d.f2 + locationR16 13056 *
        radiusPolynomialRoot16 (d.f0 13056 165) (d.f1 13056 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13056 : ℝ) ^ 8 * (mA 13056 : ℝ) ^ 8 *
        ((((4276649159 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4276649159 / 1000000000000000000)) * ((1426762619 / 1000000000000000000)) * (126 / 100) +
          2 * (((1426762619 / 1000000000000000000)) ^ 2 + 2 * ((4276649159 / 1000000000000000000)) * ((42865371 / 125000000000000000))) +
          6 * ((1426762619 / 1000000000000000000)) * ((42865371 / 125000000000000000)) * (126 / 100) + 8 * ((42865371 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13056) *
          (32 * (((4276649159 / 1000000000000000000) : ℝ) + (1426762619 / 1000000000000000000) + (42865371 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13056 : ℝ) ^ 16 *
      (d.w0 13056 165 + d.w1 13056 165 * √(π / 2) + 2 * d.w2 13056 165 +
        energyR16 13056 * radiusPolynomialRoot16 (d.w0 13056 165) (d.w1 13056 165)
          (d.w2 13056 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13056 : ℝ) ^ 16 *
        (((1687285071 / 100000000000000000000) : ℝ) + ((150058893 / 12500000000000000000)) * (126 / 100) + 2 * ((342673 / 78125000000000000)) +
          (2 * (370 / 100 : ℝ) / 13056) *
          (32 * (((1687285071 / 100000000000000000000) : ℝ) + (150058893 / 12500000000000000000) + (342673 / 78125000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13056

/-! A coarse bound on the actual paper statistics constant at dimension 13057. -/
namespace BstLean.Part266.Row13057
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13055 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13055 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13055 128 ≤ (13309 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13309 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13057) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13057 : ℕ))
    (by norm_num : (13057 : ℕ) ≤ 16384)
  have ht : paperTail256 13057 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13057 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13057 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13057 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13057 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13057 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13055 128 * √(2 / (13057 : ℝ)) *
      (√(13057 : ℝ) + paperT0 13057 + paperTail256 13057) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13057 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13057 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13057 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13055 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13055 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13057 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13057

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13057
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13057 (61 / 100) 165 (17 / (100 * 13057)) (26 / (10 * 13057)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13057 (61 / 100) 165 (17 / (100 * 13057)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (438516697 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (268678381 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4094581961 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13057 / 13057 * (61 / 100)) ^ 4 * inverseRadius8 (13057 - 1) /
            envelopeGap 13057 (61 / 100) 165 (17 / (100 * 13057)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13057

namespace BstLean.Part266.Row13057
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13057 165 ≤ (427583311 / 100000000000000000)
  f1 : (tableEnvelope C).f1 13057 165 ≤ (713245043 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (85714347 / 250000000000000000)
  w0 : (tableEnvelope C).w0 13057 165 ≤ (1686897973 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13057 165 ≤ (600097801 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13057 165 ≤ (54815083 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (438516697 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (438516697 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (268678381 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4094581961 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((36083 / 10000000) : ℝ) ≤ √(17 / (100 * 13057) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13057) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2094079027 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18326155523 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13057) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13057) ≤ (54155379 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13057) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13057 * (165 : ℝ) ^ 2 + 26 / (10 * 13057) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13057) : ℝ)) (tA 13057 * 165 ^ 2 + 26 / (10 * 13057)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((36083 / 10000000))) * ((438516697 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((36083 / 10000000)) ^ 3) * ((268678381 / 200000000000000000000000))) + ((4094581961 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((36083 / 10000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13057) : ℝ)) d.D d.V d.P (√(tA 13057) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((36083 / 10000000)) ^ 2 * (((2094079027 / 1000000000000000)) * ((18326155523 / 500000000000000000)))) + ((4094581961 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13057) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((36083 / 10000000)) * ((438516697 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13057) : ℝ)) (tA 13057 * 165 ^ 2 + 26 / (10 * 13057)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((438516697 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((36083 / 10000000)) ^ 2) * ((268678381 / 200000000000000000000000)) + ((4094581961 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13057) : ℝ)) (√(26 / (10 * 13057) : ℝ)) d.D d.V d.P (√(tA 13057) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((36083 / 10000000)) * (((2094079027 / 1000000000000000)) * ((18326155523 / 500000000000000000))) + ((4094581961 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13057) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((438516697 / 100000000000000000000) : ℝ) + ((4094581961 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13057

namespace BstLean.Part266.Row13057
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13057 165 ∧
    0 ≤ (tableEnvelope C).f1 13057 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13057 165 ∧
    0 ≤ (tableEnvelope C).w1 13057 165 ∧ 0 ≤ (tableEnvelope C).w2 13057 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13057 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13057 165 ∧ 0 ≤ d.f1 13057 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13057 165 ∧ 0 ≤ d.w1 13057 165 ∧ 0 ≤ d.w2 13057 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13057 ≤ 2 * (228 / 100 : ℝ) / 13057 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13057 ≤ 2 * (370 / 100 : ℝ) / 13057 := by
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
    (completeRAData (tableEnvelope C) 13057 165).locationBound 13057 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13057 165).energyBound 13057 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13057 165) (d.f1 13057 165) d.f2 ≤
      32 * (((427583311 / 100000000000000000) : ℝ) + (713245043 / 500000000000000000) + (85714347 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13057 165) (d.w1 13057 165)
      (d.w2 13057 165) ≤
      32 * (((1686897973 / 100000000000000000000) : ℝ) + (600097801 / 50000000000000000000) + (54815083 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13057 165) (d.f1 13057 165) d.f2 ≤
      ((427583311 / 100000000000000000) : ℝ) ^ 2 + 2 * ((427583311 / 100000000000000000)) * ((713245043 / 500000000000000000)) * (126 / 100) +
      2 * (((713245043 / 500000000000000000)) ^ 2 + 2 * ((427583311 / 100000000000000000)) * ((85714347 / 250000000000000000))) +
      6 * ((713245043 / 500000000000000000)) * ((85714347 / 250000000000000000)) * (126 / 100) + 8 * ((85714347 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13057 165) (d.f1 13057 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13057 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13057 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13057 165) (d.f1 13057 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13057 165) (d.w1 13057 165) (d.w2 13057 165)
  have hwexpr0 : 0 ≤ d.w0 13057 165 + d.w1 13057 165 * √(π / 2) +
      2 * d.w2 13057 165 + energyR16 13057 *
      radiusPolynomialRoot16 (d.w0 13057 165) (d.w1 13057 165) (d.w2 13057 165) := by
    positivity
  constructor
  · change (13057 : ℝ) ^ 8 * (mA 13057 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13057 165) (d.f1 13057 165) d.f2 + locationR16 13057 *
        radiusPolynomialRoot16 (d.f0 13057 165) (d.f1 13057 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13057 : ℝ) ^ 8 * (mA 13057 : ℝ) ^ 8 *
        ((((427583311 / 100000000000000000) : ℝ) ^ 2 + 2 * ((427583311 / 100000000000000000)) * ((713245043 / 500000000000000000)) * (126 / 100) +
          2 * (((713245043 / 500000000000000000)) ^ 2 + 2 * ((427583311 / 100000000000000000)) * ((85714347 / 250000000000000000))) +
          6 * ((713245043 / 500000000000000000)) * ((85714347 / 250000000000000000)) * (126 / 100) + 8 * ((85714347 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13057) *
          (32 * (((427583311 / 100000000000000000) : ℝ) + (713245043 / 500000000000000000) + (85714347 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13057 : ℝ) ^ 16 *
      (d.w0 13057 165 + d.w1 13057 165 * √(π / 2) + 2 * d.w2 13057 165 +
        energyR16 13057 * radiusPolynomialRoot16 (d.w0 13057 165) (d.w1 13057 165)
          (d.w2 13057 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13057 : ℝ) ^ 16 *
        (((1686897973 / 100000000000000000000) : ℝ) + ((600097801 / 50000000000000000000)) * (126 / 100) + 2 * ((54815083 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13057) *
          (32 * (((1686897973 / 100000000000000000000) : ℝ) + (600097801 / 50000000000000000000) + (54815083 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13057

/-! A coarse bound on the actual paper statistics constant at dimension 13058. -/
namespace BstLean.Part266.Row13058
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13056 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13056 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13056 128 ≤ (13310 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13310 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13058) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13058 : ℕ))
    (by norm_num : (13058 : ℕ) ≤ 16384)
  have ht : paperTail256 13058 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13058 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13058 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13058 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13058 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13058 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13056 128 * √(2 / (13058 : ℝ)) *
      (√(13058 : ℝ) + paperT0 13058 + paperTail256 13058) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13058 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13058 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13058 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13056 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13056 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13058 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13058

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13058
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13058 (61 / 100) 165 (17 / (100 * 13058)) (26 / (10 * 13058)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13058 (61 / 100) 165 (17 / (100 * 13058)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (27400997 / 6250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1342980421 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1023012603 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13058 / 13058 * (61 / 100)) ^ 4 * inverseRadius8 (13058 - 1) /
            envelopeGap 13058 (61 / 100) 165 (17 / (100 * 13058)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13058

namespace BstLean.Part266.Row13058
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13058 165 ≤ (4275013911 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13058 165 ≤ (285243369 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (34279173 / 100000000000000000)
  w0 : (tableEnvelope C).w0 13058 165 ≤ (1686510311 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13058 165 ≤ (599959907 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13058 165 ≤ (109604979 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (27400997 / 6250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (27400997 / 6250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1342980421 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1023012603 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1804081 / 500000000) : ℝ) ≤ √(17 / (100 * 13058) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13058) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1046919233 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36646697273 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13058) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13058) ≤ (846113 / 7812500000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13058) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13058 * (165 : ℝ) ^ 2 + 26 / (10 * 13058) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13058) : ℝ)) (tA 13058 * 165 ^ 2 + 26 / (10 * 13058)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1804081 / 500000000))) * ((27400997 / 6250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1804081 / 500000000)) ^ 3) * ((1342980421 / 1000000000000000000000000))) + ((1023012603 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1804081 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13058) : ℝ)) d.D d.V d.P (√(tA 13058) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1804081 / 500000000)) ^ 2 * (((1046919233 / 500000000000000)) * ((36646697273 / 1000000000000000000)))) + ((1023012603 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13058) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1804081 / 500000000)) * ((27400997 / 6250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13058) : ℝ)) (tA 13058 * 165 ^ 2 + 26 / (10 * 13058)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((27400997 / 6250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1804081 / 500000000)) ^ 2) * ((1342980421 / 1000000000000000000000000)) + ((1023012603 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13058) : ℝ)) (√(26 / (10 * 13058) : ℝ)) d.D d.V d.P (√(tA 13058) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1804081 / 500000000)) * (((1046919233 / 500000000000000)) * ((36646697273 / 1000000000000000000))) + ((1023012603 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13058) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((27400997 / 6250000000000000000) : ℝ) + ((1023012603 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13058

namespace BstLean.Part266.Row13058
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13058 165 ∧
    0 ≤ (tableEnvelope C).f1 13058 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13058 165 ∧
    0 ≤ (tableEnvelope C).w1 13058 165 ∧ 0 ≤ (tableEnvelope C).w2 13058 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13058 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13058 165 ∧ 0 ≤ d.f1 13058 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13058 165 ∧ 0 ≤ d.w1 13058 165 ∧ 0 ≤ d.w2 13058 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13058 ≤ 2 * (228 / 100 : ℝ) / 13058 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13058 ≤ 2 * (370 / 100 : ℝ) / 13058 := by
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
    (completeRAData (tableEnvelope C) 13058 165).locationBound 13058 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13058 165).energyBound 13058 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13058 165) (d.f1 13058 165) d.f2 ≤
      32 * (((4275013911 / 1000000000000000000) : ℝ) + (285243369 / 200000000000000000) + (34279173 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13058 165) (d.w1 13058 165)
      (d.w2 13058 165) ≤
      32 * (((1686510311 / 100000000000000000000) : ℝ) + (599959907 / 50000000000000000000) + (109604979 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13058 165) (d.f1 13058 165) d.f2 ≤
      ((4275013911 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4275013911 / 1000000000000000000)) * ((285243369 / 200000000000000000)) * (126 / 100) +
      2 * (((285243369 / 200000000000000000)) ^ 2 + 2 * ((4275013911 / 1000000000000000000)) * ((34279173 / 100000000000000000))) +
      6 * ((285243369 / 200000000000000000)) * ((34279173 / 100000000000000000)) * (126 / 100) + 8 * ((34279173 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13058 165) (d.f1 13058 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13058 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13058 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13058 165) (d.f1 13058 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13058 165) (d.w1 13058 165) (d.w2 13058 165)
  have hwexpr0 : 0 ≤ d.w0 13058 165 + d.w1 13058 165 * √(π / 2) +
      2 * d.w2 13058 165 + energyR16 13058 *
      radiusPolynomialRoot16 (d.w0 13058 165) (d.w1 13058 165) (d.w2 13058 165) := by
    positivity
  constructor
  · change (13058 : ℝ) ^ 8 * (mA 13058 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13058 165) (d.f1 13058 165) d.f2 + locationR16 13058 *
        radiusPolynomialRoot16 (d.f0 13058 165) (d.f1 13058 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13058 : ℝ) ^ 8 * (mA 13058 : ℝ) ^ 8 *
        ((((4275013911 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4275013911 / 1000000000000000000)) * ((285243369 / 200000000000000000)) * (126 / 100) +
          2 * (((285243369 / 200000000000000000)) ^ 2 + 2 * ((4275013911 / 1000000000000000000)) * ((34279173 / 100000000000000000))) +
          6 * ((285243369 / 200000000000000000)) * ((34279173 / 100000000000000000)) * (126 / 100) + 8 * ((34279173 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13058) *
          (32 * (((4275013911 / 1000000000000000000) : ℝ) + (285243369 / 200000000000000000) + (34279173 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13058 : ℝ) ^ 16 *
      (d.w0 13058 165 + d.w1 13058 165 * √(π / 2) + 2 * d.w2 13058 165 +
        energyR16 13058 * radiusPolynomialRoot16 (d.w0 13058 165) (d.w1 13058 165)
          (d.w2 13058 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13058 : ℝ) ^ 16 *
        (((1686510311 / 100000000000000000000) : ℝ) + ((599959907 / 50000000000000000000)) * (126 / 100) + 2 * ((109604979 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13058) *
          (32 * (((1686510311 / 100000000000000000000) : ℝ) + (599959907 / 50000000000000000000) + (109604979 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13058

/-! A coarse bound on the actual paper statistics constant at dimension 13059. -/
namespace BstLean.Part266.Row13059
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13057 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13057 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13057 128 ≤ (13311 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13311 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13059) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13059 : ℕ))
    (by norm_num : (13059 : ℕ) ≤ 16384)
  have ht : paperTail256 13059 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13059 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13059 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13059 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13059 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13059 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13057 128 * √(2 / (13059 : ℝ)) *
      (√(13059 : ℝ) + paperT0 13059 + paperTail256 13059) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13059 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13059 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13059 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13057 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13057 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13059 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13059

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13059
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13059 (61 / 100) 165 (17 / (100 * 13059)) (26 / (10 * 13059)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13059 (61 / 100) 165 (17 / (100 * 13059)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (438315239 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (671284547 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (255595039 / 62500000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13059 / 13059 * (61 / 100)) ^ 4 * inverseRadius8 (13059 - 1) /
            envelopeGap 13059 (61 / 100) 165 (17 / (100 * 13059)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13059

namespace BstLean.Part266.Row13059
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13059 165 ≤ (2137097493 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13059 165 ≤ (1425943691 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (342726091 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13059 165 ≤ (1686122779 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13059 165 ≤ (1199644117 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13059 165 ≤ (438319201 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (438315239 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (438315239 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (671284547 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (255595039 / 62500000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((451003 / 125000000) : ℝ) ≤ √(17 / (100 * 13059) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13059) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1046798977 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18320542391 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13059) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13059) ≤ (10829417 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13059) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13059 * (165 : ℝ) ^ 2 + 26 / (10 * 13059) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13059) : ℝ)) (tA 13059 * 165 ^ 2 + 26 / (10 * 13059)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((451003 / 125000000))) * ((438315239 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((451003 / 125000000)) ^ 3) * ((671284547 / 500000000000000000000000))) + ((255595039 / 62500000000000000000000)) * (3 / 2 * (39895 / 100000) / ((451003 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13059) : ℝ)) d.D d.V d.P (√(tA 13059) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((451003 / 125000000)) ^ 2 * (((1046798977 / 500000000000000)) * ((18320542391 / 500000000000000000)))) + ((255595039 / 62500000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13059) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((451003 / 125000000)) * ((438315239 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13059) : ℝ)) (tA 13059 * 165 ^ 2 + 26 / (10 * 13059)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((438315239 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((451003 / 125000000)) ^ 2) * ((671284547 / 500000000000000000000000)) + ((255595039 / 62500000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13059) : ℝ)) (√(26 / (10 * 13059) : ℝ)) d.D d.V d.P (√(tA 13059) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((451003 / 125000000)) * (((1046798977 / 500000000000000)) * ((18320542391 / 500000000000000000))) + ((255595039 / 62500000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13059) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((438315239 / 100000000000000000000) : ℝ) + ((255595039 / 62500000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13059

namespace BstLean.Part266.Row13059
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13059 165 ∧
    0 ≤ (tableEnvelope C).f1 13059 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13059 165 ∧
    0 ≤ (tableEnvelope C).w1 13059 165 ∧ 0 ≤ (tableEnvelope C).w2 13059 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13059 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13059 165 ∧ 0 ≤ d.f1 13059 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13059 165 ∧ 0 ≤ d.w1 13059 165 ∧ 0 ≤ d.w2 13059 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13059 ≤ 2 * (228 / 100 : ℝ) / 13059 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13059 ≤ 2 * (370 / 100 : ℝ) / 13059 := by
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
    (completeRAData (tableEnvelope C) 13059 165).locationBound 13059 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13059 165).energyBound 13059 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13059 165) (d.f1 13059 165) d.f2 ≤
      32 * (((2137097493 / 500000000000000000) : ℝ) + (1425943691 / 1000000000000000000) + (342726091 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13059 165) (d.w1 13059 165)
      (d.w2 13059 165) ≤
      32 * (((1686122779 / 100000000000000000000) : ℝ) + (1199644117 / 100000000000000000000) + (438319201 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13059 165) (d.f1 13059 165) d.f2 ≤
      ((2137097493 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2137097493 / 500000000000000000)) * ((1425943691 / 1000000000000000000)) * (126 / 100) +
      2 * (((1425943691 / 1000000000000000000)) ^ 2 + 2 * ((2137097493 / 500000000000000000)) * ((342726091 / 1000000000000000000))) +
      6 * ((1425943691 / 1000000000000000000)) * ((342726091 / 1000000000000000000)) * (126 / 100) + 8 * ((342726091 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13059 165) (d.f1 13059 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13059 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13059 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13059 165) (d.f1 13059 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13059 165) (d.w1 13059 165) (d.w2 13059 165)
  have hwexpr0 : 0 ≤ d.w0 13059 165 + d.w1 13059 165 * √(π / 2) +
      2 * d.w2 13059 165 + energyR16 13059 *
      radiusPolynomialRoot16 (d.w0 13059 165) (d.w1 13059 165) (d.w2 13059 165) := by
    positivity
  constructor
  · change (13059 : ℝ) ^ 8 * (mA 13059 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13059 165) (d.f1 13059 165) d.f2 + locationR16 13059 *
        radiusPolynomialRoot16 (d.f0 13059 165) (d.f1 13059 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13059 : ℝ) ^ 8 * (mA 13059 : ℝ) ^ 8 *
        ((((2137097493 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2137097493 / 500000000000000000)) * ((1425943691 / 1000000000000000000)) * (126 / 100) +
          2 * (((1425943691 / 1000000000000000000)) ^ 2 + 2 * ((2137097493 / 500000000000000000)) * ((342726091 / 1000000000000000000))) +
          6 * ((1425943691 / 1000000000000000000)) * ((342726091 / 1000000000000000000)) * (126 / 100) + 8 * ((342726091 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13059) *
          (32 * (((2137097493 / 500000000000000000) : ℝ) + (1425943691 / 1000000000000000000) + (342726091 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13059 : ℝ) ^ 16 *
      (d.w0 13059 165 + d.w1 13059 165 * √(π / 2) + 2 * d.w2 13059 165 +
        energyR16 13059 * radiusPolynomialRoot16 (d.w0 13059 165) (d.w1 13059 165)
          (d.w2 13059 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13059 : ℝ) ^ 16 *
        (((1686122779 / 100000000000000000000) : ℝ) + ((1199644117 / 100000000000000000000)) * (126 / 100) + 2 * ((438319201 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13059) *
          (32 * (((1686122779 / 100000000000000000000) : ℝ) + (1199644117 / 100000000000000000000) + (438319201 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13059

/-! A coarse bound on the actual paper statistics constant at dimension 13060. -/
namespace BstLean.Part266.Row13060
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13058 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13058 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13058 128 ≤ (13312 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13312 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13060) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13060 : ℕ))
    (by norm_num : (13060 : ℕ) ≤ 16384)
  have ht : paperTail256 13060 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13060 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13060 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13060 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13060 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13060 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13058 128 * √(2 / (13060 : ℝ)) *
      (√(13060 : ℝ) + paperT0 13060 + paperTail256 13060) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13060 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13060 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13060 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13058 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13058 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13060 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13060

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13060
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13060 (61 / 100) 165 (17 / (100 * 13060)) (26 / (10 * 13060)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13060 (61 / 100) 165 (17 / (100 * 13060)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (438214557 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (671078963 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2043496299 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13060 / 13060 * (61 / 100)) ^ 4 * inverseRadius8 (13060 - 1) /
            envelopeGap 13060 (61 / 100) 165 (17 / (100 * 13060)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13060

namespace BstLean.Part266.Row13060
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13060 165 ≤ (2136688169 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13060 165 ≤ (44552207 / 31250000000000000)
  f2 : (tableEnvelope C).f2 ≤ (342660473 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13060 165 ≤ (1685735379 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13060 165 ≤ (1199368511 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13060 165 ≤ (438218517 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (438214557 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (438214557 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (671078963 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2043496299 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1803943 / 500000000) : ℝ) ≤ √(17 / (100 * 13060) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13060) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (130834843 / 62500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18317736801 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13060) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13060) ≤ (54142939 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13060) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13060 * (165 : ℝ) ^ 2 + 26 / (10 * 13060) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13060) : ℝ)) (tA 13060 * 165 ^ 2 + 26 / (10 * 13060)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1803943 / 500000000))) * ((438214557 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1803943 / 500000000)) ^ 3) * ((671078963 / 500000000000000000000000))) + ((2043496299 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1803943 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13060) : ℝ)) d.D d.V d.P (√(tA 13060) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1803943 / 500000000)) ^ 2 * (((130834843 / 62500000000000)) * ((18317736801 / 500000000000000000)))) + ((2043496299 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13060) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1803943 / 500000000)) * ((438214557 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13060) : ℝ)) (tA 13060 * 165 ^ 2 + 26 / (10 * 13060)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((438214557 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1803943 / 500000000)) ^ 2) * ((671078963 / 500000000000000000000000)) + ((2043496299 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13060) : ℝ)) (√(26 / (10 * 13060) : ℝ)) d.D d.V d.P (√(tA 13060) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1803943 / 500000000)) * (((130834843 / 62500000000000)) * ((18317736801 / 500000000000000000))) + ((2043496299 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13060) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((438214557 / 100000000000000000000) : ℝ) + ((2043496299 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13060

namespace BstLean.Part266.Row13060
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13060 165 ∧
    0 ≤ (tableEnvelope C).f1 13060 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13060 165 ∧
    0 ≤ (tableEnvelope C).w1 13060 165 ∧ 0 ≤ (tableEnvelope C).w2 13060 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13060 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13060 165 ∧ 0 ≤ d.f1 13060 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13060 165 ∧ 0 ≤ d.w1 13060 165 ∧ 0 ≤ d.w2 13060 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13060 ≤ 2 * (228 / 100 : ℝ) / 13060 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13060 ≤ 2 * (370 / 100 : ℝ) / 13060 := by
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
    (completeRAData (tableEnvelope C) 13060 165).locationBound 13060 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13060 165).energyBound 13060 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13060 165) (d.f1 13060 165) d.f2 ≤
      32 * (((2136688169 / 500000000000000000) : ℝ) + (44552207 / 31250000000000000) + (342660473 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13060 165) (d.w1 13060 165)
      (d.w2 13060 165) ≤
      32 * (((1685735379 / 100000000000000000000) : ℝ) + (1199368511 / 100000000000000000000) + (438218517 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13060 165) (d.f1 13060 165) d.f2 ≤
      ((2136688169 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2136688169 / 500000000000000000)) * ((44552207 / 31250000000000000)) * (126 / 100) +
      2 * (((44552207 / 31250000000000000)) ^ 2 + 2 * ((2136688169 / 500000000000000000)) * ((342660473 / 1000000000000000000))) +
      6 * ((44552207 / 31250000000000000)) * ((342660473 / 1000000000000000000)) * (126 / 100) + 8 * ((342660473 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13060 165) (d.f1 13060 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13060 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13060 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13060 165) (d.f1 13060 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13060 165) (d.w1 13060 165) (d.w2 13060 165)
  have hwexpr0 : 0 ≤ d.w0 13060 165 + d.w1 13060 165 * √(π / 2) +
      2 * d.w2 13060 165 + energyR16 13060 *
      radiusPolynomialRoot16 (d.w0 13060 165) (d.w1 13060 165) (d.w2 13060 165) := by
    positivity
  constructor
  · change (13060 : ℝ) ^ 8 * (mA 13060 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13060 165) (d.f1 13060 165) d.f2 + locationR16 13060 *
        radiusPolynomialRoot16 (d.f0 13060 165) (d.f1 13060 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13060 : ℝ) ^ 8 * (mA 13060 : ℝ) ^ 8 *
        ((((2136688169 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2136688169 / 500000000000000000)) * ((44552207 / 31250000000000000)) * (126 / 100) +
          2 * (((44552207 / 31250000000000000)) ^ 2 + 2 * ((2136688169 / 500000000000000000)) * ((342660473 / 1000000000000000000))) +
          6 * ((44552207 / 31250000000000000)) * ((342660473 / 1000000000000000000)) * (126 / 100) + 8 * ((342660473 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13060) *
          (32 * (((2136688169 / 500000000000000000) : ℝ) + (44552207 / 31250000000000000) + (342660473 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13060 : ℝ) ^ 16 *
      (d.w0 13060 165 + d.w1 13060 165 * √(π / 2) + 2 * d.w2 13060 165 +
        energyR16 13060 * radiusPolynomialRoot16 (d.w0 13060 165) (d.w1 13060 165)
          (d.w2 13060 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13060 : ℝ) ^ 16 *
        (((1685735379 / 100000000000000000000) : ℝ) + ((1199368511 / 100000000000000000000)) * (126 / 100) + 2 * ((438218517 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13060) *
          (32 * (((1685735379 / 100000000000000000000) : ℝ) + (1199368511 / 100000000000000000000) + (438218517 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13060

/-! A coarse bound on the actual paper statistics constant at dimension 13061. -/
namespace BstLean.Part266.Row13061
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13059 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13059 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13059 128 ≤ (13313 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13313 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13061) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13061 : ℕ))
    (by norm_num : (13061 : ℕ) ≤ 16384)
  have ht : paperTail256 13061 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13061 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13061 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13061 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13061 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13061 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13059 128 * √(2 / (13061 : ℝ)) *
      (√(13061 : ℝ) + paperT0 13061 + paperTail256 13061) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13061 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13061 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13061 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13059 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13059 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13061 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13061

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13061
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13061 (61 / 100) 165 (17 / (100 * 13061)) (26 / (10 * 13061)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13061 (61 / 100) 165 (17 / (100 * 13061)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (87622781 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (670873457 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1021116583 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13061 / 13061 * (61 / 100)) ^ 4 * inverseRadius8 (13061 - 1) /
            envelopeGap 13061 (61 / 100) 165 (17 / (100 * 13061)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13061

namespace BstLean.Part266.Row13061
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13061 165 ≤ (106813949 / 25000000000000000)
  f1 : (tableEnvelope C).f1 13061 165 ≤ (35634941 / 25000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (42824359 / 125000000000000000)
  w0 : (tableEnvelope C).w0 13061 165 ≤ (842674053 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13061 165 ≤ (4683957 / 390625000000000000)
  w2 : (tableEnvelope C).w2 13061 165 ≤ (219058931 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (87622781 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (87622781 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (670873457 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1021116583 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((901937 / 250000000) : ℝ) ≤ √(17 / (100 * 13061) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13061) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1046558533 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36629863691 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13061) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13061) ≤ (108277587 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13061) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13061 * (165 : ℝ) ^ 2 + 26 / (10 * 13061) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13061) : ℝ)) (tA 13061 * 165 ^ 2 + 26 / (10 * 13061)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((901937 / 250000000))) * ((87622781 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((901937 / 250000000)) ^ 3) * ((670873457 / 500000000000000000000000))) + ((1021116583 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((901937 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13061) : ℝ)) d.D d.V d.P (√(tA 13061) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((901937 / 250000000)) ^ 2 * (((1046558533 / 500000000000000)) * ((36629863691 / 1000000000000000000)))) + ((1021116583 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13061) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((901937 / 250000000)) * ((87622781 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13061) : ℝ)) (tA 13061 * 165 ^ 2 + 26 / (10 * 13061)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((87622781 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((901937 / 250000000)) ^ 2) * ((670873457 / 500000000000000000000000)) + ((1021116583 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13061) : ℝ)) (√(26 / (10 * 13061) : ℝ)) d.D d.V d.P (√(tA 13061) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((901937 / 250000000)) * (((1046558533 / 500000000000000)) * ((36629863691 / 1000000000000000000))) + ((1021116583 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13061) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((87622781 / 20000000000000000000) : ℝ) + ((1021116583 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13061

namespace BstLean.Part266.Row13061
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13061 165 ∧
    0 ≤ (tableEnvelope C).f1 13061 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13061 165 ∧
    0 ≤ (tableEnvelope C).w1 13061 165 ∧ 0 ≤ (tableEnvelope C).w2 13061 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13061 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13061 165 ∧ 0 ≤ d.f1 13061 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13061 165 ∧ 0 ≤ d.w1 13061 165 ∧ 0 ≤ d.w2 13061 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13061 ≤ 2 * (228 / 100 : ℝ) / 13061 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13061 ≤ 2 * (370 / 100 : ℝ) / 13061 := by
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
    (completeRAData (tableEnvelope C) 13061 165).locationBound 13061 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13061 165).energyBound 13061 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13061 165) (d.f1 13061 165) d.f2 ≤
      32 * (((106813949 / 25000000000000000) : ℝ) + (35634941 / 25000000000000000) + (42824359 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13061 165) (d.w1 13061 165)
      (d.w2 13061 165) ≤
      32 * (((842674053 / 50000000000000000000) : ℝ) + (4683957 / 390625000000000000) + (219058931 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13061 165) (d.f1 13061 165) d.f2 ≤
      ((106813949 / 25000000000000000) : ℝ) ^ 2 + 2 * ((106813949 / 25000000000000000)) * ((35634941 / 25000000000000000)) * (126 / 100) +
      2 * (((35634941 / 25000000000000000)) ^ 2 + 2 * ((106813949 / 25000000000000000)) * ((42824359 / 125000000000000000))) +
      6 * ((35634941 / 25000000000000000)) * ((42824359 / 125000000000000000)) * (126 / 100) + 8 * ((42824359 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13061 165) (d.f1 13061 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13061 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13061 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13061 165) (d.f1 13061 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13061 165) (d.w1 13061 165) (d.w2 13061 165)
  have hwexpr0 : 0 ≤ d.w0 13061 165 + d.w1 13061 165 * √(π / 2) +
      2 * d.w2 13061 165 + energyR16 13061 *
      radiusPolynomialRoot16 (d.w0 13061 165) (d.w1 13061 165) (d.w2 13061 165) := by
    positivity
  constructor
  · change (13061 : ℝ) ^ 8 * (mA 13061 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13061 165) (d.f1 13061 165) d.f2 + locationR16 13061 *
        radiusPolynomialRoot16 (d.f0 13061 165) (d.f1 13061 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13061 : ℝ) ^ 8 * (mA 13061 : ℝ) ^ 8 *
        ((((106813949 / 25000000000000000) : ℝ) ^ 2 + 2 * ((106813949 / 25000000000000000)) * ((35634941 / 25000000000000000)) * (126 / 100) +
          2 * (((35634941 / 25000000000000000)) ^ 2 + 2 * ((106813949 / 25000000000000000)) * ((42824359 / 125000000000000000))) +
          6 * ((35634941 / 25000000000000000)) * ((42824359 / 125000000000000000)) * (126 / 100) + 8 * ((42824359 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13061) *
          (32 * (((106813949 / 25000000000000000) : ℝ) + (35634941 / 25000000000000000) + (42824359 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13061 : ℝ) ^ 16 *
      (d.w0 13061 165 + d.w1 13061 165 * √(π / 2) + 2 * d.w2 13061 165 +
        energyR16 13061 * radiusPolynomialRoot16 (d.w0 13061 165) (d.w1 13061 165)
          (d.w2 13061 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13061 : ℝ) ^ 16 *
        (((842674053 / 50000000000000000000) : ℝ) + ((4683957 / 390625000000000000)) * (126 / 100) + 2 * ((219058931 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13061) *
          (32 * (((842674053 / 50000000000000000000) : ℝ) + (4683957 / 390625000000000000) + (219058931 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13061

/-! A coarse bound on the actual paper statistics constant at dimension 13062. -/
namespace BstLean.Part266.Row13062
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13060 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13060 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13060 128 ≤ (13314 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13314 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13062) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13062 : ℕ))
    (by norm_num : (13062 : ℕ) ≤ 16384)
  have ht : paperTail256 13062 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13062 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13062 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13062 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13062 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13062 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13060 128 * √(2 / (13062 : ℝ)) *
      (√(13062 : ℝ) + paperT0 13062 + paperTail256 13062) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13062 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13062 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13062 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13060 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13060 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13062 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13062

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13062
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13062 (61 / 100) 165 (17 / (100 * 13062)) (26 / (10 * 13062)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13062 (61 / 100) 165 (17 / (100 * 13062)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (109503321 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (67066803 / 50000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (63780341 / 15625000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13062 / 13062 * (61 / 100)) ^ 4 * inverseRadius8 (13062 - 1) /
            envelopeGap 13062 (61 / 100) 165 (17 / (100 * 13062)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13062

namespace BstLean.Part266.Row13062
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13062 165 ≤ (4271739857 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13062 165 ≤ (1425124743 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (342529291 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13062 165 ≤ (1684960963 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13062 165 ≤ (299704391 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 13062 165 ≤ (438017239 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (109503321 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (109503321 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (67066803 / 50000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (63780341 / 15625000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((360761 / 100000000) : ℝ) ≤ √(17 / (100 * 13062) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13062) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2092876691 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18312127539 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13062) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13062) ≤ (54134649 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13062) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13062 * (165 : ℝ) ^ 2 + 26 / (10 * 13062) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13062) : ℝ)) (tA 13062 * 165 ^ 2 + 26 / (10 * 13062)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((360761 / 100000000))) * ((109503321 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((360761 / 100000000)) ^ 3) * ((67066803 / 50000000000000000000000))) + ((63780341 / 15625000000000000000000)) * (3 / 2 * (39895 / 100000) / ((360761 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13062) : ℝ)) d.D d.V d.P (√(tA 13062) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((360761 / 100000000)) ^ 2 * (((2092876691 / 1000000000000000)) * ((18312127539 / 500000000000000000)))) + ((63780341 / 15625000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13062) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((360761 / 100000000)) * ((109503321 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13062) : ℝ)) (tA 13062 * 165 ^ 2 + 26 / (10 * 13062)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((109503321 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((360761 / 100000000)) ^ 2) * ((67066803 / 50000000000000000000000)) + ((63780341 / 15625000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13062) : ℝ)) (√(26 / (10 * 13062) : ℝ)) d.D d.V d.P (√(tA 13062) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((360761 / 100000000)) * (((2092876691 / 1000000000000000)) * ((18312127539 / 500000000000000000))) + ((63780341 / 15625000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13062) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((109503321 / 25000000000000000000) : ℝ) + ((63780341 / 15625000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13062

namespace BstLean.Part266.Row13062
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13062 165 ∧
    0 ≤ (tableEnvelope C).f1 13062 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13062 165 ∧
    0 ≤ (tableEnvelope C).w1 13062 165 ∧ 0 ≤ (tableEnvelope C).w2 13062 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13062 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13062 165 ∧ 0 ≤ d.f1 13062 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13062 165 ∧ 0 ≤ d.w1 13062 165 ∧ 0 ≤ d.w2 13062 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13062 ≤ 2 * (228 / 100 : ℝ) / 13062 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13062 ≤ 2 * (370 / 100 : ℝ) / 13062 := by
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
    (completeRAData (tableEnvelope C) 13062 165).locationBound 13062 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13062 165).energyBound 13062 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13062 165) (d.f1 13062 165) d.f2 ≤
      32 * (((4271739857 / 1000000000000000000) : ℝ) + (1425124743 / 1000000000000000000) + (342529291 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13062 165) (d.w1 13062 165)
      (d.w2 13062 165) ≤
      32 * (((1684960963 / 100000000000000000000) : ℝ) + (299704391 / 25000000000000000000) + (438017239 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13062 165) (d.f1 13062 165) d.f2 ≤
      ((4271739857 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4271739857 / 1000000000000000000)) * ((1425124743 / 1000000000000000000)) * (126 / 100) +
      2 * (((1425124743 / 1000000000000000000)) ^ 2 + 2 * ((4271739857 / 1000000000000000000)) * ((342529291 / 1000000000000000000))) +
      6 * ((1425124743 / 1000000000000000000)) * ((342529291 / 1000000000000000000)) * (126 / 100) + 8 * ((342529291 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13062 165) (d.f1 13062 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13062 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13062 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13062 165) (d.f1 13062 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13062 165) (d.w1 13062 165) (d.w2 13062 165)
  have hwexpr0 : 0 ≤ d.w0 13062 165 + d.w1 13062 165 * √(π / 2) +
      2 * d.w2 13062 165 + energyR16 13062 *
      radiusPolynomialRoot16 (d.w0 13062 165) (d.w1 13062 165) (d.w2 13062 165) := by
    positivity
  constructor
  · change (13062 : ℝ) ^ 8 * (mA 13062 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13062 165) (d.f1 13062 165) d.f2 + locationR16 13062 *
        radiusPolynomialRoot16 (d.f0 13062 165) (d.f1 13062 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13062 : ℝ) ^ 8 * (mA 13062 : ℝ) ^ 8 *
        ((((4271739857 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4271739857 / 1000000000000000000)) * ((1425124743 / 1000000000000000000)) * (126 / 100) +
          2 * (((1425124743 / 1000000000000000000)) ^ 2 + 2 * ((4271739857 / 1000000000000000000)) * ((342529291 / 1000000000000000000))) +
          6 * ((1425124743 / 1000000000000000000)) * ((342529291 / 1000000000000000000)) * (126 / 100) + 8 * ((342529291 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13062) *
          (32 * (((4271739857 / 1000000000000000000) : ℝ) + (1425124743 / 1000000000000000000) + (342529291 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13062 : ℝ) ^ 16 *
      (d.w0 13062 165 + d.w1 13062 165 * √(π / 2) + 2 * d.w2 13062 165 +
        energyR16 13062 * radiusPolynomialRoot16 (d.w0 13062 165) (d.w1 13062 165)
          (d.w2 13062 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13062 : ℝ) ^ 16 *
        (((1684960963 / 100000000000000000000) : ℝ) + ((299704391 / 25000000000000000000)) * (126 / 100) + 2 * ((438017239 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13062) *
          (32 * (((1684960963 / 100000000000000000000) : ℝ) + (299704391 / 25000000000000000000) + (438017239 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13062

/-! A coarse bound on the actual paper statistics constant at dimension 13063. -/
namespace BstLean.Part266.Row13063
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13061 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13061 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13061 128 ≤ (13315 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13315 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13063) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13063 : ℕ))
    (by norm_num : (13063 : ℕ) ≤ 16384)
  have ht : paperTail256 13063 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13063 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13063 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13063 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13063 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13063 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13061 128 * √(2 / (13063 : ℝ)) *
      (√(13063 : ℝ) + paperT0 13063 + paperTail256 13063) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13063 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13063 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13063 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13061 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13061 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13063 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13063

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13063
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13063 (61 / 100) 165 (17 / (100 * 13063)) (26 / (10 * 13063)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13063 (61 / 100) 165 (17 / (100 * 13063)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (87582539 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1340925363 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4079419073 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13063 / 13063 * (61 / 100)) ^ 4 * inverseRadius8 (13063 - 1) /
            envelopeGap 13063 (61 / 100) 165 (17 / (100 * 13063)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13063

namespace BstLean.Part266.Row13063
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13063 165 ≤ (1067730507 / 250000000000000000)
  f1 : (tableEnvelope C).f1 13063 165 ≤ (1424851933 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (34246373 / 100000000000000000)
  w0 : (tableEnvelope C).w0 13063 165 ≤ (1684573951 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13063 165 ≤ (1198542227 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13063 165 ≤ (437916647 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (87582539 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (87582539 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1340925363 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4079419073 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((225467 / 62500000) : ℝ) ≤ √(17 / (100 * 13063) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13063) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (523159091 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (146474591 / 4000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13063) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13063) ≤ (10826101 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13063) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13063 * (165 : ℝ) ^ 2 + 26 / (10 * 13063) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13063) : ℝ)) (tA 13063 * 165 ^ 2 + 26 / (10 * 13063)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((225467 / 62500000))) * ((87582539 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((225467 / 62500000)) ^ 3) * ((1340925363 / 1000000000000000000000000))) + ((4079419073 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((225467 / 62500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13063) : ℝ)) d.D d.V d.P (√(tA 13063) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((225467 / 62500000)) ^ 2 * (((523159091 / 250000000000000)) * ((146474591 / 4000000000000000)))) + ((4079419073 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13063) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((225467 / 62500000)) * ((87582539 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13063) : ℝ)) (tA 13063 * 165 ^ 2 + 26 / (10 * 13063)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((87582539 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((225467 / 62500000)) ^ 2) * ((1340925363 / 1000000000000000000000000)) + ((4079419073 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13063) : ℝ)) (√(26 / (10 * 13063) : ℝ)) d.D d.V d.P (√(tA 13063) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((225467 / 62500000)) * (((523159091 / 250000000000000)) * ((146474591 / 4000000000000000))) + ((4079419073 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13063) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((87582539 / 20000000000000000000) : ℝ) + ((4079419073 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13063

namespace BstLean.Part266.Row13063
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13063 165 ∧
    0 ≤ (tableEnvelope C).f1 13063 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13063 165 ∧
    0 ≤ (tableEnvelope C).w1 13063 165 ∧ 0 ≤ (tableEnvelope C).w2 13063 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13063 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13063 165 ∧ 0 ≤ d.f1 13063 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13063 165 ∧ 0 ≤ d.w1 13063 165 ∧ 0 ≤ d.w2 13063 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13063 ≤ 2 * (228 / 100 : ℝ) / 13063 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13063 ≤ 2 * (370 / 100 : ℝ) / 13063 := by
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
    (completeRAData (tableEnvelope C) 13063 165).locationBound 13063 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13063 165).energyBound 13063 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13063 165) (d.f1 13063 165) d.f2 ≤
      32 * (((1067730507 / 250000000000000000) : ℝ) + (1424851933 / 1000000000000000000) + (34246373 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13063 165) (d.w1 13063 165)
      (d.w2 13063 165) ≤
      32 * (((1684573951 / 100000000000000000000) : ℝ) + (1198542227 / 100000000000000000000) + (437916647 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13063 165) (d.f1 13063 165) d.f2 ≤
      ((1067730507 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1067730507 / 250000000000000000)) * ((1424851933 / 1000000000000000000)) * (126 / 100) +
      2 * (((1424851933 / 1000000000000000000)) ^ 2 + 2 * ((1067730507 / 250000000000000000)) * ((34246373 / 100000000000000000))) +
      6 * ((1424851933 / 1000000000000000000)) * ((34246373 / 100000000000000000)) * (126 / 100) + 8 * ((34246373 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13063 165) (d.f1 13063 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13063 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13063 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13063 165) (d.f1 13063 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13063 165) (d.w1 13063 165) (d.w2 13063 165)
  have hwexpr0 : 0 ≤ d.w0 13063 165 + d.w1 13063 165 * √(π / 2) +
      2 * d.w2 13063 165 + energyR16 13063 *
      radiusPolynomialRoot16 (d.w0 13063 165) (d.w1 13063 165) (d.w2 13063 165) := by
    positivity
  constructor
  · change (13063 : ℝ) ^ 8 * (mA 13063 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13063 165) (d.f1 13063 165) d.f2 + locationR16 13063 *
        radiusPolynomialRoot16 (d.f0 13063 165) (d.f1 13063 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13063 : ℝ) ^ 8 * (mA 13063 : ℝ) ^ 8 *
        ((((1067730507 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1067730507 / 250000000000000000)) * ((1424851933 / 1000000000000000000)) * (126 / 100) +
          2 * (((1424851933 / 1000000000000000000)) ^ 2 + 2 * ((1067730507 / 250000000000000000)) * ((34246373 / 100000000000000000))) +
          6 * ((1424851933 / 1000000000000000000)) * ((34246373 / 100000000000000000)) * (126 / 100) + 8 * ((34246373 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13063) *
          (32 * (((1067730507 / 250000000000000000) : ℝ) + (1424851933 / 1000000000000000000) + (34246373 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13063 : ℝ) ^ 16 *
      (d.w0 13063 165 + d.w1 13063 165 * √(π / 2) + 2 * d.w2 13063 165 +
        energyR16 13063 * radiusPolynomialRoot16 (d.w0 13063 165) (d.w1 13063 165)
          (d.w2 13063 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13063 : ℝ) ^ 16 *
        (((1684573951 / 100000000000000000000) : ℝ) + ((1198542227 / 100000000000000000000)) * (126 / 100) + 2 * ((437916647 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13063) *
          (32 * (((1684573951 / 100000000000000000000) : ℝ) + (1198542227 / 100000000000000000000) + (437916647 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13063

/-! A coarse bound on the actual paper statistics constant at dimension 13064. -/
namespace BstLean.Part266.Row13064
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13062 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13062 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13062 128 ≤ (13316 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13316 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13064) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13064 : ℕ))
    (by norm_num : (13064 : ℕ) ≤ 16384)
  have ht : paperTail256 13064 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13064 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13064 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13064 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13064 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13064 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13062 128 * √(2 / (13064 : ℝ)) *
      (√(13064 : ℝ) + paperT0 13064 + paperTail256 13064) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13064 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13064 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13064 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13062 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13062 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13064 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13064

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13064
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13064 (61 / 100) 165 (17 / (100 * 13064)) (26 / (10 * 13064)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13064 (61 / 100) 165 (17 / (100 * 13064)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (87562427 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1340514823 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4076898077 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13064 / 13064 * (61 / 100)) ^ 4 * inverseRadius8 (13064 - 1) /
            envelopeGap 13064 (61 / 100) 165 (17 / (100 * 13064)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13064

namespace BstLean.Part266.Row13064
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13064 165 ≤ (4270104471 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13064 165 ≤ (712289603 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (171199093 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13064 165 ≤ (1684187067 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13064 165 ≤ (1198266977 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13064 165 ≤ (87563217 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (87562427 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (87562427 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1340514823 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4076898077 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1803667 / 500000000) : ℝ) ≤ √(17 / (100 * 13064) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13064) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2092396079 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36613041707 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13064) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13064) ≤ (108252723 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13064) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13064 * (165 : ℝ) ^ 2 + 26 / (10 * 13064) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13064) : ℝ)) (tA 13064 * 165 ^ 2 + 26 / (10 * 13064)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1803667 / 500000000))) * ((87562427 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1803667 / 500000000)) ^ 3) * ((1340514823 / 1000000000000000000000000))) + ((4076898077 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1803667 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13064) : ℝ)) d.D d.V d.P (√(tA 13064) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1803667 / 500000000)) ^ 2 * (((2092396079 / 1000000000000000)) * ((36613041707 / 1000000000000000000)))) + ((4076898077 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13064) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1803667 / 500000000)) * ((87562427 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13064) : ℝ)) (tA 13064 * 165 ^ 2 + 26 / (10 * 13064)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((87562427 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1803667 / 500000000)) ^ 2) * ((1340514823 / 1000000000000000000000000)) + ((4076898077 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13064) : ℝ)) (√(26 / (10 * 13064) : ℝ)) d.D d.V d.P (√(tA 13064) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1803667 / 500000000)) * (((2092396079 / 1000000000000000)) * ((36613041707 / 1000000000000000000))) + ((4076898077 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13064) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((87562427 / 20000000000000000000) : ℝ) + ((4076898077 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13064

namespace BstLean.Part266.Row13064
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13064 165 ∧
    0 ≤ (tableEnvelope C).f1 13064 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13064 165 ∧
    0 ≤ (tableEnvelope C).w1 13064 165 ∧ 0 ≤ (tableEnvelope C).w2 13064 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13064 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13064 165 ∧ 0 ≤ d.f1 13064 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13064 165 ∧ 0 ≤ d.w1 13064 165 ∧ 0 ≤ d.w2 13064 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13064 ≤ 2 * (228 / 100 : ℝ) / 13064 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13064 ≤ 2 * (370 / 100 : ℝ) / 13064 := by
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
    (completeRAData (tableEnvelope C) 13064 165).locationBound 13064 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13064 165).energyBound 13064 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13064 165) (d.f1 13064 165) d.f2 ≤
      32 * (((4270104471 / 1000000000000000000) : ℝ) + (712289603 / 500000000000000000) + (171199093 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13064 165) (d.w1 13064 165)
      (d.w2 13064 165) ≤
      32 * (((1684187067 / 100000000000000000000) : ℝ) + (1198266977 / 100000000000000000000) + (87563217 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13064 165) (d.f1 13064 165) d.f2 ≤
      ((4270104471 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4270104471 / 1000000000000000000)) * ((712289603 / 500000000000000000)) * (126 / 100) +
      2 * (((712289603 / 500000000000000000)) ^ 2 + 2 * ((4270104471 / 1000000000000000000)) * ((171199093 / 500000000000000000))) +
      6 * ((712289603 / 500000000000000000)) * ((171199093 / 500000000000000000)) * (126 / 100) + 8 * ((171199093 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13064 165) (d.f1 13064 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13064 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13064 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13064 165) (d.f1 13064 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13064 165) (d.w1 13064 165) (d.w2 13064 165)
  have hwexpr0 : 0 ≤ d.w0 13064 165 + d.w1 13064 165 * √(π / 2) +
      2 * d.w2 13064 165 + energyR16 13064 *
      radiusPolynomialRoot16 (d.w0 13064 165) (d.w1 13064 165) (d.w2 13064 165) := by
    positivity
  constructor
  · change (13064 : ℝ) ^ 8 * (mA 13064 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13064 165) (d.f1 13064 165) d.f2 + locationR16 13064 *
        radiusPolynomialRoot16 (d.f0 13064 165) (d.f1 13064 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13064 : ℝ) ^ 8 * (mA 13064 : ℝ) ^ 8 *
        ((((4270104471 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4270104471 / 1000000000000000000)) * ((712289603 / 500000000000000000)) * (126 / 100) +
          2 * (((712289603 / 500000000000000000)) ^ 2 + 2 * ((4270104471 / 1000000000000000000)) * ((171199093 / 500000000000000000))) +
          6 * ((712289603 / 500000000000000000)) * ((171199093 / 500000000000000000)) * (126 / 100) + 8 * ((171199093 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13064) *
          (32 * (((4270104471 / 1000000000000000000) : ℝ) + (712289603 / 500000000000000000) + (171199093 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13064 : ℝ) ^ 16 *
      (d.w0 13064 165 + d.w1 13064 165 * √(π / 2) + 2 * d.w2 13064 165 +
        energyR16 13064 * radiusPolynomialRoot16 (d.w0 13064 165) (d.w1 13064 165)
          (d.w2 13064 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13064 : ℝ) ^ 16 *
        (((1684187067 / 100000000000000000000) : ℝ) + ((1198266977 / 100000000000000000000)) * (126 / 100) + 2 * ((87563217 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13064) *
          (32 * (((1684187067 / 100000000000000000000) : ℝ) + (1198266977 / 100000000000000000000) + (87563217 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13064

/-! A coarse bound on the actual paper statistics constant at dimension 13065. -/
namespace BstLean.Part266.Row13065
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13063 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13063 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13063 128 ≤ (13317 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13317 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13065) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13065 : ℕ))
    (by norm_num : (13065 : ℕ) ≤ 16384)
  have ht : paperTail256 13065 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13065 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13065 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13065 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13065 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13065 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13063 128 * √(2 / (13065 : ℝ)) *
      (√(13065 : ℝ) + paperT0 13065 + paperTail256 13065) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13065 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13065 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13065 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13063 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13063 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13065 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13065

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13065
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13065 (61 / 100) 165 (17 / (100 * 13065)) (26 / (10 * 13065)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13065 (61 / 100) 165 (17 / (100 * 13065)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (437711607 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1340104441 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1018594709 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13065 / 13065 * (61 / 100)) ^ 4 * inverseRadius8 (13065 - 1) /
            envelopeGap 13065 (61 / 100) 165 (17 / (100 * 13065)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13065

namespace BstLean.Part266.Row13065
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13065 165 ≤ (426928719 / 100000000000000000)
  f1 : (tableEnvelope C).f1 13065 165 ≤ (1424306567 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (342332663 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13065 165 ≤ (841900157 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13065 165 ≤ (598995909 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13065 165 ≤ (218857777 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (437711607 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (437711607 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1340104441 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1018594709 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((901799 / 250000000) : ℝ) ≤ √(17 / (100 * 13065) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13065) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2092155843 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36607436963 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13065) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13065) ≤ (108244437 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13065) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13065 * (165 : ℝ) ^ 2 + 26 / (10 * 13065) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13065) : ℝ)) (tA 13065 * 165 ^ 2 + 26 / (10 * 13065)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((901799 / 250000000))) * ((437711607 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((901799 / 250000000)) ^ 3) * ((1340104441 / 1000000000000000000000000))) + ((1018594709 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((901799 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13065) : ℝ)) d.D d.V d.P (√(tA 13065) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((901799 / 250000000)) ^ 2 * (((2092155843 / 1000000000000000)) * ((36607436963 / 1000000000000000000)))) + ((1018594709 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13065) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((901799 / 250000000)) * ((437711607 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13065) : ℝ)) (tA 13065 * 165 ^ 2 + 26 / (10 * 13065)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((437711607 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((901799 / 250000000)) ^ 2) * ((1340104441 / 1000000000000000000000000)) + ((1018594709 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13065) : ℝ)) (√(26 / (10 * 13065) : ℝ)) d.D d.V d.P (√(tA 13065) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((901799 / 250000000)) * (((2092155843 / 1000000000000000)) * ((36607436963 / 1000000000000000000))) + ((1018594709 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13065) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((437711607 / 100000000000000000000) : ℝ) + ((1018594709 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13065

namespace BstLean.Part266.Row13065
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13065 165 ∧
    0 ≤ (tableEnvelope C).f1 13065 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13065 165 ∧
    0 ≤ (tableEnvelope C).w1 13065 165 ∧ 0 ≤ (tableEnvelope C).w2 13065 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13065 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13065 165 ∧ 0 ≤ d.f1 13065 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13065 165 ∧ 0 ≤ d.w1 13065 165 ∧ 0 ≤ d.w2 13065 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13065 ≤ 2 * (228 / 100 : ℝ) / 13065 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13065 ≤ 2 * (370 / 100 : ℝ) / 13065 := by
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
    (completeRAData (tableEnvelope C) 13065 165).locationBound 13065 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13065 165).energyBound 13065 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13065 165) (d.f1 13065 165) d.f2 ≤
      32 * (((426928719 / 100000000000000000) : ℝ) + (1424306567 / 1000000000000000000) + (342332663 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13065 165) (d.w1 13065 165)
      (d.w2 13065 165) ≤
      32 * (((841900157 / 50000000000000000000) : ℝ) + (598995909 / 50000000000000000000) + (218857777 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13065 165) (d.f1 13065 165) d.f2 ≤
      ((426928719 / 100000000000000000) : ℝ) ^ 2 + 2 * ((426928719 / 100000000000000000)) * ((1424306567 / 1000000000000000000)) * (126 / 100) +
      2 * (((1424306567 / 1000000000000000000)) ^ 2 + 2 * ((426928719 / 100000000000000000)) * ((342332663 / 1000000000000000000))) +
      6 * ((1424306567 / 1000000000000000000)) * ((342332663 / 1000000000000000000)) * (126 / 100) + 8 * ((342332663 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13065 165) (d.f1 13065 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13065 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13065 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13065 165) (d.f1 13065 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13065 165) (d.w1 13065 165) (d.w2 13065 165)
  have hwexpr0 : 0 ≤ d.w0 13065 165 + d.w1 13065 165 * √(π / 2) +
      2 * d.w2 13065 165 + energyR16 13065 *
      radiusPolynomialRoot16 (d.w0 13065 165) (d.w1 13065 165) (d.w2 13065 165) := by
    positivity
  constructor
  · change (13065 : ℝ) ^ 8 * (mA 13065 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13065 165) (d.f1 13065 165) d.f2 + locationR16 13065 *
        radiusPolynomialRoot16 (d.f0 13065 165) (d.f1 13065 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13065 : ℝ) ^ 8 * (mA 13065 : ℝ) ^ 8 *
        ((((426928719 / 100000000000000000) : ℝ) ^ 2 + 2 * ((426928719 / 100000000000000000)) * ((1424306567 / 1000000000000000000)) * (126 / 100) +
          2 * (((1424306567 / 1000000000000000000)) ^ 2 + 2 * ((426928719 / 100000000000000000)) * ((342332663 / 1000000000000000000))) +
          6 * ((1424306567 / 1000000000000000000)) * ((342332663 / 1000000000000000000)) * (126 / 100) + 8 * ((342332663 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13065) *
          (32 * (((426928719 / 100000000000000000) : ℝ) + (1424306567 / 1000000000000000000) + (342332663 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13065 : ℝ) ^ 16 *
      (d.w0 13065 165 + d.w1 13065 165 * √(π / 2) + 2 * d.w2 13065 165 +
        energyR16 13065 * radiusPolynomialRoot16 (d.w0 13065 165) (d.w1 13065 165)
          (d.w2 13065 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13065 : ℝ) ^ 16 *
        (((841900157 / 50000000000000000000) : ℝ) + ((598995909 / 50000000000000000000)) * (126 / 100) + 2 * ((218857777 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13065) *
          (32 * (((841900157 / 50000000000000000000) : ℝ) + (598995909 / 50000000000000000000) + (218857777 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13065

/-! A coarse bound on the actual paper statistics constant at dimension 13066. -/
namespace BstLean.Part266.Row13066
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13064 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13064 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13064 128 ≤ (13318 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13318 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13066) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13066 : ℕ))
    (by norm_num : (13066 : ℕ) ≤ 16384)
  have ht : paperTail256 13066 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13066 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13066 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13066 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13066 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13066 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13064 128 * √(2 / (13066 : ℝ)) *
      (√(13066 : ℝ) + paperT0 13066 + paperTail256 13066) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13066 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13066 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13066 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13064 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13064 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13066 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13066

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13066
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13066 (61 / 100) 165 (17 / (100 * 13066)) (26 / (10 * 13066)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13066 (61 / 100) 165 (17 / (100 * 13066)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (437611109 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (267938843 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1017965337 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13066 / 13066 * (61 / 100)) ^ 4 * inverseRadius8 (13066 - 1) /
            envelopeGap 13066 (61 / 100) 165 (17 / (100 * 13066)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13066

namespace BstLean.Part266.Row13066
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13066 165 ≤ (2134235089 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13066 165 ≤ (356008503 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (171133579 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13066 165 ≤ (210426711 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 13066 165 ≤ (299429187 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 13066 165 ≤ (218807527 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (437611109 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (437611109 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (267938843 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1017965337 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1803529 / 500000000) : ℝ) ≤ √(17 / (100 * 13066) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13066) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2091915651 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36601833493 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13066) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13066) ≤ (108236153 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13066) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13066 * (165 : ℝ) ^ 2 + 26 / (10 * 13066) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13066) : ℝ)) (tA 13066 * 165 ^ 2 + 26 / (10 * 13066)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1803529 / 500000000))) * ((437611109 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1803529 / 500000000)) ^ 3) * ((267938843 / 200000000000000000000000))) + ((1017965337 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1803529 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13066) : ℝ)) d.D d.V d.P (√(tA 13066) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1803529 / 500000000)) ^ 2 * (((2091915651 / 1000000000000000)) * ((36601833493 / 1000000000000000000)))) + ((1017965337 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13066) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1803529 / 500000000)) * ((437611109 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13066) : ℝ)) (tA 13066 * 165 ^ 2 + 26 / (10 * 13066)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((437611109 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1803529 / 500000000)) ^ 2) * ((267938843 / 200000000000000000000000)) + ((1017965337 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13066) : ℝ)) (√(26 / (10 * 13066) : ℝ)) d.D d.V d.P (√(tA 13066) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1803529 / 500000000)) * (((2091915651 / 1000000000000000)) * ((36601833493 / 1000000000000000000))) + ((1017965337 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13066) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((437611109 / 100000000000000000000) : ℝ) + ((1017965337 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13066

namespace BstLean.Part266.Row13066
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13066 165 ∧
    0 ≤ (tableEnvelope C).f1 13066 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13066 165 ∧
    0 ≤ (tableEnvelope C).w1 13066 165 ∧ 0 ≤ (tableEnvelope C).w2 13066 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13066 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13066 165 ∧ 0 ≤ d.f1 13066 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13066 165 ∧ 0 ≤ d.w1 13066 165 ∧ 0 ≤ d.w2 13066 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13066 ≤ 2 * (228 / 100 : ℝ) / 13066 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13066 ≤ 2 * (370 / 100 : ℝ) / 13066 := by
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
    (completeRAData (tableEnvelope C) 13066 165).locationBound 13066 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13066 165).energyBound 13066 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13066 165) (d.f1 13066 165) d.f2 ≤
      32 * (((2134235089 / 500000000000000000) : ℝ) + (356008503 / 250000000000000000) + (171133579 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13066 165) (d.w1 13066 165)
      (d.w2 13066 165) ≤
      32 * (((210426711 / 12500000000000000000) : ℝ) + (299429187 / 25000000000000000000) + (218807527 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13066 165) (d.f1 13066 165) d.f2 ≤
      ((2134235089 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2134235089 / 500000000000000000)) * ((356008503 / 250000000000000000)) * (126 / 100) +
      2 * (((356008503 / 250000000000000000)) ^ 2 + 2 * ((2134235089 / 500000000000000000)) * ((171133579 / 500000000000000000))) +
      6 * ((356008503 / 250000000000000000)) * ((171133579 / 500000000000000000)) * (126 / 100) + 8 * ((171133579 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13066 165) (d.f1 13066 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13066 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13066 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13066 165) (d.f1 13066 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13066 165) (d.w1 13066 165) (d.w2 13066 165)
  have hwexpr0 : 0 ≤ d.w0 13066 165 + d.w1 13066 165 * √(π / 2) +
      2 * d.w2 13066 165 + energyR16 13066 *
      radiusPolynomialRoot16 (d.w0 13066 165) (d.w1 13066 165) (d.w2 13066 165) := by
    positivity
  constructor
  · change (13066 : ℝ) ^ 8 * (mA 13066 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13066 165) (d.f1 13066 165) d.f2 + locationR16 13066 *
        radiusPolynomialRoot16 (d.f0 13066 165) (d.f1 13066 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13066 : ℝ) ^ 8 * (mA 13066 : ℝ) ^ 8 *
        ((((2134235089 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2134235089 / 500000000000000000)) * ((356008503 / 250000000000000000)) * (126 / 100) +
          2 * (((356008503 / 250000000000000000)) ^ 2 + 2 * ((2134235089 / 500000000000000000)) * ((171133579 / 500000000000000000))) +
          6 * ((356008503 / 250000000000000000)) * ((171133579 / 500000000000000000)) * (126 / 100) + 8 * ((171133579 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13066) *
          (32 * (((2134235089 / 500000000000000000) : ℝ) + (356008503 / 250000000000000000) + (171133579 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13066 : ℝ) ^ 16 *
      (d.w0 13066 165 + d.w1 13066 165 * √(π / 2) + 2 * d.w2 13066 165 +
        energyR16 13066 * radiusPolynomialRoot16 (d.w0 13066 165) (d.w1 13066 165)
          (d.w2 13066 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13066 : ℝ) ^ 16 *
        (((210426711 / 12500000000000000000) : ℝ) + ((299429187 / 25000000000000000000)) * (126 / 100) + 2 * ((218807527 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13066) *
          (32 * (((210426711 / 12500000000000000000) : ℝ) + (299429187 / 25000000000000000000) + (218807527 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13066

/-! A coarse bound on the actual paper statistics constant at dimension 13067. -/
namespace BstLean.Part266.Row13067
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13065 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13065 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13065 128 ≤ (13319 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13319 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13067) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13067 : ℕ))
    (by norm_num : (13067 : ℕ) ≤ 16384)
  have ht : paperTail256 13067 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13067 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13067 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13067 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13067 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13067 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13065 128 * √(2 / (13067 : ℝ)) *
      (√(13067 : ℝ) + paperT0 13067 + paperTail256 13067) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13067 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13067 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13067 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13065 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13065 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13067 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13067

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13067
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13067 (61 / 100) 165 (17 / (100 * 13067)) (26 / (10 * 13067)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13067 (61 / 100) 165 (17 / (100 * 13067)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (437510643 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1339284147 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4069345611 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13067 / 13067 * (61 / 100)) ^ 4 * inverseRadius8 (13067 - 1) /
            envelopeGap 13067 (61 / 100) 165 (17 / (100 * 13067)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13067

namespace BstLean.Part266.Row13067
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13067 165 ≤ (4267653443 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13067 165 ≤ (177970193 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (342201673 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13067 165 ≤ (841513597 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13067 165 ≤ (1197441769 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13067 165 ≤ (87502917 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (437510643 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (437510643 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1339284147 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4069345611 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((90173 / 25000000) : ℝ) ≤ √(17 / (100 * 13067) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13067) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (522918877 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36596231323 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13067) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13067) ≤ (108227869 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13067) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13067 * (165 : ℝ) ^ 2 + 26 / (10 * 13067) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13067) : ℝ)) (tA 13067 * 165 ^ 2 + 26 / (10 * 13067)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((90173 / 25000000))) * ((437510643 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((90173 / 25000000)) ^ 3) * ((1339284147 / 1000000000000000000000000))) + ((4069345611 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((90173 / 25000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13067) : ℝ)) d.D d.V d.P (√(tA 13067) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((90173 / 25000000)) ^ 2 * (((522918877 / 250000000000000)) * ((36596231323 / 1000000000000000000)))) + ((4069345611 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13067) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((90173 / 25000000)) * ((437510643 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13067) : ℝ)) (tA 13067 * 165 ^ 2 + 26 / (10 * 13067)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((437510643 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((90173 / 25000000)) ^ 2) * ((1339284147 / 1000000000000000000000000)) + ((4069345611 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13067) : ℝ)) (√(26 / (10 * 13067) : ℝ)) d.D d.V d.P (√(tA 13067) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((90173 / 25000000)) * (((522918877 / 250000000000000)) * ((36596231323 / 1000000000000000000))) + ((4069345611 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13067) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((437510643 / 100000000000000000000) : ℝ) + ((4069345611 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13067

namespace BstLean.Part266.Row13067
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13067 165 ∧
    0 ≤ (tableEnvelope C).f1 13067 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13067 165 ∧
    0 ≤ (tableEnvelope C).w1 13067 165 ∧ 0 ≤ (tableEnvelope C).w2 13067 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13067 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13067 165 ∧ 0 ≤ d.f1 13067 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13067 165 ∧ 0 ≤ d.w1 13067 165 ∧ 0 ≤ d.w2 13067 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13067 ≤ 2 * (228 / 100 : ℝ) / 13067 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13067 ≤ 2 * (370 / 100 : ℝ) / 13067 := by
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
    (completeRAData (tableEnvelope C) 13067 165).locationBound 13067 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13067 165).energyBound 13067 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13067 165) (d.f1 13067 165) d.f2 ≤
      32 * (((4267653443 / 1000000000000000000) : ℝ) + (177970193 / 125000000000000000) + (342201673 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13067 165) (d.w1 13067 165)
      (d.w2 13067 165) ≤
      32 * (((841513597 / 50000000000000000000) : ℝ) + (1197441769 / 100000000000000000000) + (87502917 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13067 165) (d.f1 13067 165) d.f2 ≤
      ((4267653443 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4267653443 / 1000000000000000000)) * ((177970193 / 125000000000000000)) * (126 / 100) +
      2 * (((177970193 / 125000000000000000)) ^ 2 + 2 * ((4267653443 / 1000000000000000000)) * ((342201673 / 1000000000000000000))) +
      6 * ((177970193 / 125000000000000000)) * ((342201673 / 1000000000000000000)) * (126 / 100) + 8 * ((342201673 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13067 165) (d.f1 13067 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13067 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13067 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13067 165) (d.f1 13067 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13067 165) (d.w1 13067 165) (d.w2 13067 165)
  have hwexpr0 : 0 ≤ d.w0 13067 165 + d.w1 13067 165 * √(π / 2) +
      2 * d.w2 13067 165 + energyR16 13067 *
      radiusPolynomialRoot16 (d.w0 13067 165) (d.w1 13067 165) (d.w2 13067 165) := by
    positivity
  constructor
  · change (13067 : ℝ) ^ 8 * (mA 13067 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13067 165) (d.f1 13067 165) d.f2 + locationR16 13067 *
        radiusPolynomialRoot16 (d.f0 13067 165) (d.f1 13067 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13067 : ℝ) ^ 8 * (mA 13067 : ℝ) ^ 8 *
        ((((4267653443 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4267653443 / 1000000000000000000)) * ((177970193 / 125000000000000000)) * (126 / 100) +
          2 * (((177970193 / 125000000000000000)) ^ 2 + 2 * ((4267653443 / 1000000000000000000)) * ((342201673 / 1000000000000000000))) +
          6 * ((177970193 / 125000000000000000)) * ((342201673 / 1000000000000000000)) * (126 / 100) + 8 * ((342201673 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13067) *
          (32 * (((4267653443 / 1000000000000000000) : ℝ) + (177970193 / 125000000000000000) + (342201673 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13067 : ℝ) ^ 16 *
      (d.w0 13067 165 + d.w1 13067 165 * √(π / 2) + 2 * d.w2 13067 165 +
        energyR16 13067 * radiusPolynomialRoot16 (d.w0 13067 165) (d.w1 13067 165)
          (d.w2 13067 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13067 : ℝ) ^ 16 *
        (((841513597 / 50000000000000000000) : ℝ) + ((1197441769 / 100000000000000000000)) * (126 / 100) + 2 * ((87502917 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13067) *
          (32 * (((841513597 / 50000000000000000000) : ℝ) + (1197441769 / 100000000000000000000) + (87502917 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13067

/-! A coarse bound on the actual paper statistics constant at dimension 13068. -/
namespace BstLean.Part266.Row13068
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13066 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13066 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13066 128 ≤ (13320 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13320 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13068) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13068 : ℕ))
    (by norm_num : (13068 : ℕ) ≤ 16384)
  have ht : paperTail256 13068 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13068 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13068 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13068 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13068 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13068 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13066 128 * √(2 / (13068 : ℝ)) *
      (√(13068 : ℝ) + paperT0 13068 + paperTail256 13068) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13068 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13068 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13068 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13066 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13066 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13068 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13068

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13068
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13068 (61 / 100) 165 (17 / (100 * 13068)) (26 / (10 * 13068)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13068 (61 / 100) 165 (17 / (100 * 13068)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (437410207 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (267774847 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (32534653 / 8000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13068 / 13068 * (61 / 100)) ^ 4 * inverseRadius8 (13068 - 1) /
            envelopeGap 13068 (61 / 100) 165 (17 / (100 * 13068)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13068

namespace BstLean.Part266.Row13068
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13068 165 ≤ (2133418489 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13068 165 ≤ (1423489161 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (171068103 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13068 165 ≤ (420660207 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 13068 165 ≤ (598583439 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13068 165 ≤ (437414147 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (437410207 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (437410207 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (267774847 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (32534653 / 8000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1803391 / 500000000) : ℝ) ≤ √(17 / (100 * 13068) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13068) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2091435409 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36590630427 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13068) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13068) ≤ (108219587 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13068) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13068 * (165 : ℝ) ^ 2 + 26 / (10 * 13068) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13068) : ℝ)) (tA 13068 * 165 ^ 2 + 26 / (10 * 13068)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1803391 / 500000000))) * ((437410207 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1803391 / 500000000)) ^ 3) * ((267774847 / 200000000000000000000000))) + ((32534653 / 8000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1803391 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13068) : ℝ)) d.D d.V d.P (√(tA 13068) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1803391 / 500000000)) ^ 2 * (((2091435409 / 1000000000000000)) * ((36590630427 / 1000000000000000000)))) + ((32534653 / 8000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13068) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1803391 / 500000000)) * ((437410207 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13068) : ℝ)) (tA 13068 * 165 ^ 2 + 26 / (10 * 13068)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((437410207 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1803391 / 500000000)) ^ 2) * ((267774847 / 200000000000000000000000)) + ((32534653 / 8000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13068) : ℝ)) (√(26 / (10 * 13068) : ℝ)) d.D d.V d.P (√(tA 13068) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1803391 / 500000000)) * (((2091435409 / 1000000000000000)) * ((36590630427 / 1000000000000000000))) + ((32534653 / 8000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13068) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((437410207 / 100000000000000000000) : ℝ) + ((32534653 / 8000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13068

namespace BstLean.Part266.Row13068
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13068 165 ∧
    0 ≤ (tableEnvelope C).f1 13068 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13068 165 ∧
    0 ≤ (tableEnvelope C).w1 13068 165 ∧ 0 ≤ (tableEnvelope C).w2 13068 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13068 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13068 165 ∧ 0 ≤ d.f1 13068 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13068 165 ∧ 0 ≤ d.w1 13068 165 ∧ 0 ≤ d.w2 13068 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13068 ≤ 2 * (228 / 100 : ℝ) / 13068 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13068 ≤ 2 * (370 / 100 : ℝ) / 13068 := by
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
    (completeRAData (tableEnvelope C) 13068 165).locationBound 13068 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13068 165).energyBound 13068 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13068 165) (d.f1 13068 165) d.f2 ≤
      32 * (((2133418489 / 500000000000000000) : ℝ) + (1423489161 / 1000000000000000000) + (171068103 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13068 165) (d.w1 13068 165)
      (d.w2 13068 165) ≤
      32 * (((420660207 / 25000000000000000000) : ℝ) + (598583439 / 50000000000000000000) + (437414147 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13068 165) (d.f1 13068 165) d.f2 ≤
      ((2133418489 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2133418489 / 500000000000000000)) * ((1423489161 / 1000000000000000000)) * (126 / 100) +
      2 * (((1423489161 / 1000000000000000000)) ^ 2 + 2 * ((2133418489 / 500000000000000000)) * ((171068103 / 500000000000000000))) +
      6 * ((1423489161 / 1000000000000000000)) * ((171068103 / 500000000000000000)) * (126 / 100) + 8 * ((171068103 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13068 165) (d.f1 13068 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13068 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13068 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13068 165) (d.f1 13068 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13068 165) (d.w1 13068 165) (d.w2 13068 165)
  have hwexpr0 : 0 ≤ d.w0 13068 165 + d.w1 13068 165 * √(π / 2) +
      2 * d.w2 13068 165 + energyR16 13068 *
      radiusPolynomialRoot16 (d.w0 13068 165) (d.w1 13068 165) (d.w2 13068 165) := by
    positivity
  constructor
  · change (13068 : ℝ) ^ 8 * (mA 13068 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13068 165) (d.f1 13068 165) d.f2 + locationR16 13068 *
        radiusPolynomialRoot16 (d.f0 13068 165) (d.f1 13068 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13068 : ℝ) ^ 8 * (mA 13068 : ℝ) ^ 8 *
        ((((2133418489 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2133418489 / 500000000000000000)) * ((1423489161 / 1000000000000000000)) * (126 / 100) +
          2 * (((1423489161 / 1000000000000000000)) ^ 2 + 2 * ((2133418489 / 500000000000000000)) * ((171068103 / 500000000000000000))) +
          6 * ((1423489161 / 1000000000000000000)) * ((171068103 / 500000000000000000)) * (126 / 100) + 8 * ((171068103 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13068) *
          (32 * (((2133418489 / 500000000000000000) : ℝ) + (1423489161 / 1000000000000000000) + (171068103 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13068 : ℝ) ^ 16 *
      (d.w0 13068 165 + d.w1 13068 165 * √(π / 2) + 2 * d.w2 13068 165 +
        energyR16 13068 * radiusPolynomialRoot16 (d.w0 13068 165) (d.w1 13068 165)
          (d.w2 13068 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13068 : ℝ) ^ 16 *
        (((420660207 / 25000000000000000000) : ℝ) + ((598583439 / 50000000000000000000)) * (126 / 100) + 2 * ((437414147 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13068) *
          (32 * (((420660207 / 25000000000000000000) : ℝ) + (598583439 / 50000000000000000000) + (437414147 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13068

/-! A coarse bound on the actual paper statistics constant at dimension 13069. -/
namespace BstLean.Part266.Row13069
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13067 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13067 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13067 128 ≤ (13321 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13321 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13069) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13069 : ℕ))
    (by norm_num : (13069 : ℕ) ≤ 16384)
  have ht : paperTail256 13069 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13069 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13069 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13069 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13069 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13069 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13067 128 * √(2 / (13069 : ℝ)) *
      (√(13069 : ℝ) + paperT0 13069 + paperTail256 13069) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13069 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13069 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13069 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13067 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13067 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13069 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13069

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13069
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13069 (61 / 100) 165 (17 / (100 * 13069)) (26 / (10 * 13069)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13069 (61 / 100) 165 (17 / (100 * 13069)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (437309801 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (8365403 / 6250000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4064319387 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13069 / 13069 * (61 / 100)) ^ 4 * inverseRadius8 (13069 - 1) /
            envelopeGap 13069 (61 / 100) 165 (17 / (100 * 13069)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13069

namespace BstLean.Part266.Row13069
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13069 165 ≤ (2133010393 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13069 165 ≤ (711608431 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (171035379 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13069 165 ≤ (168225459 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 13069 165 ≤ (299223019 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 13069 165 ≤ (437313739 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (437309801 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (437309801 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (8365403 / 6250000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4064319387 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((901661 / 250000000) : ℝ) ≤ √(17 / (100 * 13069) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13069) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (418239071 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36585030819 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13069) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13069) ≤ (108211307 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13069) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13069 * (165 : ℝ) ^ 2 + 26 / (10 * 13069) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13069) : ℝ)) (tA 13069 * 165 ^ 2 + 26 / (10 * 13069)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((901661 / 250000000))) * ((437309801 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((901661 / 250000000)) ^ 3) * ((8365403 / 6250000000000000000000))) + ((4064319387 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((901661 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13069) : ℝ)) d.D d.V d.P (√(tA 13069) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((901661 / 250000000)) ^ 2 * (((418239071 / 200000000000000)) * ((36585030819 / 1000000000000000000)))) + ((4064319387 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13069) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((901661 / 250000000)) * ((437309801 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13069) : ℝ)) (tA 13069 * 165 ^ 2 + 26 / (10 * 13069)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((437309801 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((901661 / 250000000)) ^ 2) * ((8365403 / 6250000000000000000000)) + ((4064319387 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13069) : ℝ)) (√(26 / (10 * 13069) : ℝ)) d.D d.V d.P (√(tA 13069) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((901661 / 250000000)) * (((418239071 / 200000000000000)) * ((36585030819 / 1000000000000000000))) + ((4064319387 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13069) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((437309801 / 100000000000000000000) : ℝ) + ((4064319387 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13069

namespace BstLean.Part266.Row13069
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13069 165 ∧
    0 ≤ (tableEnvelope C).f1 13069 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13069 165 ∧
    0 ≤ (tableEnvelope C).w1 13069 165 ∧ 0 ≤ (tableEnvelope C).w2 13069 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13069 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13069 165 ∧ 0 ≤ d.f1 13069 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13069 165 ∧ 0 ≤ d.w1 13069 165 ∧ 0 ≤ d.w2 13069 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13069 ≤ 2 * (228 / 100 : ℝ) / 13069 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13069 ≤ 2 * (370 / 100 : ℝ) / 13069 := by
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
    (completeRAData (tableEnvelope C) 13069 165).locationBound 13069 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13069 165).energyBound 13069 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13069 165) (d.f1 13069 165) d.f2 ≤
      32 * (((2133010393 / 500000000000000000) : ℝ) + (711608431 / 500000000000000000) + (171035379 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13069 165) (d.w1 13069 165)
      (d.w2 13069 165) ≤
      32 * (((168225459 / 10000000000000000000) : ℝ) + (299223019 / 25000000000000000000) + (437313739 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13069 165) (d.f1 13069 165) d.f2 ≤
      ((2133010393 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2133010393 / 500000000000000000)) * ((711608431 / 500000000000000000)) * (126 / 100) +
      2 * (((711608431 / 500000000000000000)) ^ 2 + 2 * ((2133010393 / 500000000000000000)) * ((171035379 / 500000000000000000))) +
      6 * ((711608431 / 500000000000000000)) * ((171035379 / 500000000000000000)) * (126 / 100) + 8 * ((171035379 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13069 165) (d.f1 13069 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13069 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13069 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13069 165) (d.f1 13069 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13069 165) (d.w1 13069 165) (d.w2 13069 165)
  have hwexpr0 : 0 ≤ d.w0 13069 165 + d.w1 13069 165 * √(π / 2) +
      2 * d.w2 13069 165 + energyR16 13069 *
      radiusPolynomialRoot16 (d.w0 13069 165) (d.w1 13069 165) (d.w2 13069 165) := by
    positivity
  constructor
  · change (13069 : ℝ) ^ 8 * (mA 13069 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13069 165) (d.f1 13069 165) d.f2 + locationR16 13069 *
        radiusPolynomialRoot16 (d.f0 13069 165) (d.f1 13069 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13069 : ℝ) ^ 8 * (mA 13069 : ℝ) ^ 8 *
        ((((2133010393 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2133010393 / 500000000000000000)) * ((711608431 / 500000000000000000)) * (126 / 100) +
          2 * (((711608431 / 500000000000000000)) ^ 2 + 2 * ((2133010393 / 500000000000000000)) * ((171035379 / 500000000000000000))) +
          6 * ((711608431 / 500000000000000000)) * ((171035379 / 500000000000000000)) * (126 / 100) + 8 * ((171035379 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13069) *
          (32 * (((2133010393 / 500000000000000000) : ℝ) + (711608431 / 500000000000000000) + (171035379 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13069 : ℝ) ^ 16 *
      (d.w0 13069 165 + d.w1 13069 165 * √(π / 2) + 2 * d.w2 13069 165 +
        energyR16 13069 * radiusPolynomialRoot16 (d.w0 13069 165) (d.w1 13069 165)
          (d.w2 13069 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13069 : ℝ) ^ 16 *
        (((168225459 / 10000000000000000000) : ℝ) + ((299223019 / 25000000000000000000)) * (126 / 100) + 2 * ((437313739 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13069) *
          (32 * (((168225459 / 10000000000000000000) : ℝ) + (299223019 / 25000000000000000000) + (437313739 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13069

/-! A coarse bound on the actual paper statistics constant at dimension 13070. -/
namespace BstLean.Part266.Row13070
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13068 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13068 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13068 128 ≤ (13322 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13322 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13070) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13070 : ℕ))
    (by norm_num : (13070 : ℕ) ≤ 16384)
  have ht : paperTail256 13070 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13070 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13070 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13070 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13070 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13070 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13068 128 * √(2 / (13070 : ℝ)) *
      (√(13070 : ℝ) + paperT0 13070 + paperTail256 13070) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13070 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13070 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13070 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13068 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13068 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13070 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13070

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13070
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13070 (61 / 100) 165 (17 / (100 * 13070)) (26 / (10 * 13070)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13070 (61 / 100) 165 (17 / (100 * 13070)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (437209427 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (669027441 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4061808897 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13070 / 13070 * (61 / 100)) ^ 4 * inverseRadius8 (13070 - 1) /
            envelopeGap 13070 (61 / 100) 165 (17 / (100 * 13070)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13070

namespace BstLean.Part266.Row13070
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13070 165 ≤ (4265204869 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13070 165 ≤ (28458893 / 20000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (34200533 / 100000000000000000)
  w0 : (tableEnvelope C).w0 13070 165 ≤ (1681868483 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13070 165 ≤ (299154341 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 13070 165 ≤ (218606681 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (437209427 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (437209427 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (669027441 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4061808897 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1803253 / 500000000) : ℝ) ≤ √(17 / (100 * 13070) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13070) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2090955349 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (14631773 / 400000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13070) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13070) ≤ (108203027 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13070) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13070 * (165 : ℝ) ^ 2 + 26 / (10 * 13070) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13070) : ℝ)) (tA 13070 * 165 ^ 2 + 26 / (10 * 13070)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1803253 / 500000000))) * ((437209427 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1803253 / 500000000)) ^ 3) * ((669027441 / 500000000000000000000000))) + ((4061808897 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1803253 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13070) : ℝ)) d.D d.V d.P (√(tA 13070) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1803253 / 500000000)) ^ 2 * (((2090955349 / 1000000000000000)) * ((14631773 / 400000000000000)))) + ((4061808897 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13070) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1803253 / 500000000)) * ((437209427 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13070) : ℝ)) (tA 13070 * 165 ^ 2 + 26 / (10 * 13070)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((437209427 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1803253 / 500000000)) ^ 2) * ((669027441 / 500000000000000000000000)) + ((4061808897 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13070) : ℝ)) (√(26 / (10 * 13070) : ℝ)) d.D d.V d.P (√(tA 13070) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1803253 / 500000000)) * (((2090955349 / 1000000000000000)) * ((14631773 / 400000000000000))) + ((4061808897 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13070) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((437209427 / 100000000000000000000) : ℝ) + ((4061808897 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13070

namespace BstLean.Part266.Row13070
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13070 165 ∧
    0 ≤ (tableEnvelope C).f1 13070 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13070 165 ∧
    0 ≤ (tableEnvelope C).w1 13070 165 ∧ 0 ≤ (tableEnvelope C).w2 13070 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13070 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13070 165 ∧ 0 ≤ d.f1 13070 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13070 165 ∧ 0 ≤ d.w1 13070 165 ∧ 0 ≤ d.w2 13070 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13070 ≤ 2 * (228 / 100 : ℝ) / 13070 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13070 ≤ 2 * (370 / 100 : ℝ) / 13070 := by
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
    (completeRAData (tableEnvelope C) 13070 165).locationBound 13070 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13070 165).energyBound 13070 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13070 165) (d.f1 13070 165) d.f2 ≤
      32 * (((4265204869 / 1000000000000000000) : ℝ) + (28458893 / 20000000000000000) + (34200533 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13070 165) (d.w1 13070 165)
      (d.w2 13070 165) ≤
      32 * (((1681868483 / 100000000000000000000) : ℝ) + (299154341 / 25000000000000000000) + (218606681 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13070 165) (d.f1 13070 165) d.f2 ≤
      ((4265204869 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4265204869 / 1000000000000000000)) * ((28458893 / 20000000000000000)) * (126 / 100) +
      2 * (((28458893 / 20000000000000000)) ^ 2 + 2 * ((4265204869 / 1000000000000000000)) * ((34200533 / 100000000000000000))) +
      6 * ((28458893 / 20000000000000000)) * ((34200533 / 100000000000000000)) * (126 / 100) + 8 * ((34200533 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13070 165) (d.f1 13070 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13070 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13070 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13070 165) (d.f1 13070 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13070 165) (d.w1 13070 165) (d.w2 13070 165)
  have hwexpr0 : 0 ≤ d.w0 13070 165 + d.w1 13070 165 * √(π / 2) +
      2 * d.w2 13070 165 + energyR16 13070 *
      radiusPolynomialRoot16 (d.w0 13070 165) (d.w1 13070 165) (d.w2 13070 165) := by
    positivity
  constructor
  · change (13070 : ℝ) ^ 8 * (mA 13070 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13070 165) (d.f1 13070 165) d.f2 + locationR16 13070 *
        radiusPolynomialRoot16 (d.f0 13070 165) (d.f1 13070 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13070 : ℝ) ^ 8 * (mA 13070 : ℝ) ^ 8 *
        ((((4265204869 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4265204869 / 1000000000000000000)) * ((28458893 / 20000000000000000)) * (126 / 100) +
          2 * (((28458893 / 20000000000000000)) ^ 2 + 2 * ((4265204869 / 1000000000000000000)) * ((34200533 / 100000000000000000))) +
          6 * ((28458893 / 20000000000000000)) * ((34200533 / 100000000000000000)) * (126 / 100) + 8 * ((34200533 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13070) *
          (32 * (((4265204869 / 1000000000000000000) : ℝ) + (28458893 / 20000000000000000) + (34200533 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13070 : ℝ) ^ 16 *
      (d.w0 13070 165 + d.w1 13070 165 * √(π / 2) + 2 * d.w2 13070 165 +
        energyR16 13070 * radiusPolynomialRoot16 (d.w0 13070 165) (d.w1 13070 165)
          (d.w2 13070 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13070 : ℝ) ^ 16 *
        (((1681868483 / 100000000000000000000) : ℝ) + ((299154341 / 25000000000000000000)) * (126 / 100) + 2 * ((218606681 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13070) *
          (32 * (((1681868483 / 100000000000000000000) : ℝ) + (299154341 / 25000000000000000000) + (218606681 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13070

/-! A coarse bound on the actual paper statistics constant at dimension 13071. -/
namespace BstLean.Part266.Row13071
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13069 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13069 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13069 128 ≤ (13323 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13323 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13071) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13071 : ℕ))
    (by norm_num : (13071 : ℕ) ≤ 16384)
  have ht : paperTail256 13071 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13071 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13071 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13071 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13071 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13071 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13069 128 * √(2 / (13071 : ℝ)) *
      (√(13071 : ℝ) + paperT0 13071 + paperTail256 13071) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13071 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13071 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13071 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13069 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13069 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13071 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13071

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13071
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13071 (61 / 100) 165 (17 / (100 * 13071)) (26 / (10 * 13071)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13071 (61 / 100) 165 (17 / (100 * 13071)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (437109083 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (2090071 / 1562500000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4059300153 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13071 / 13071 * (61 / 100)) ^ 4 * inverseRadius8 (13071 - 1) /
            envelopeGap 13071 (61 / 100) 165 (17 / (100 * 13071)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13071

namespace BstLean.Part266.Row13071
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13071 165 ≤ (4264389221 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13071 165 ≤ (1422672523 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (4274249 / 12500000000000000)
  w0 : (tableEnvelope C).w0 13071 165 ≤ (1681482503 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13071 165 ≤ (598171371 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13071 165 ≤ (54639127 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (437109083 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (437109083 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (2090071 / 1562500000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4059300153 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((112699 / 31250000) : ℝ) ≤ √(17 / (100 * 13071) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13071) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (522678847 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36573835457 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13071) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13071) ≤ (108194749 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13071) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13071 * (165 : ℝ) ^ 2 + 26 / (10 * 13071) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13071) : ℝ)) (tA 13071 * 165 ^ 2 + 26 / (10 * 13071)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((112699 / 31250000))) * ((437109083 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((112699 / 31250000)) ^ 3) * ((2090071 / 1562500000000000000000))) + ((4059300153 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((112699 / 31250000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13071) : ℝ)) d.D d.V d.P (√(tA 13071) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((112699 / 31250000)) ^ 2 * (((522678847 / 250000000000000)) * ((36573835457 / 1000000000000000000)))) + ((4059300153 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13071) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((112699 / 31250000)) * ((437109083 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13071) : ℝ)) (tA 13071 * 165 ^ 2 + 26 / (10 * 13071)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((437109083 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((112699 / 31250000)) ^ 2) * ((2090071 / 1562500000000000000000)) + ((4059300153 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13071) : ℝ)) (√(26 / (10 * 13071) : ℝ)) d.D d.V d.P (√(tA 13071) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((112699 / 31250000)) * (((522678847 / 250000000000000)) * ((36573835457 / 1000000000000000000))) + ((4059300153 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13071) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((437109083 / 100000000000000000000) : ℝ) + ((4059300153 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13071

namespace BstLean.Part266.Row13071
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13071 165 ∧
    0 ≤ (tableEnvelope C).f1 13071 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13071 165 ∧
    0 ≤ (tableEnvelope C).w1 13071 165 ∧ 0 ≤ (tableEnvelope C).w2 13071 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13071 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13071 165 ∧ 0 ≤ d.f1 13071 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13071 165 ∧ 0 ≤ d.w1 13071 165 ∧ 0 ≤ d.w2 13071 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13071 ≤ 2 * (228 / 100 : ℝ) / 13071 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13071 ≤ 2 * (370 / 100 : ℝ) / 13071 := by
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
    (completeRAData (tableEnvelope C) 13071 165).locationBound 13071 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13071 165).energyBound 13071 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13071 165) (d.f1 13071 165) d.f2 ≤
      32 * (((4264389221 / 1000000000000000000) : ℝ) + (1422672523 / 1000000000000000000) + (4274249 / 12500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13071 165) (d.w1 13071 165)
      (d.w2 13071 165) ≤
      32 * (((1681482503 / 100000000000000000000) : ℝ) + (598171371 / 50000000000000000000) + (54639127 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13071 165) (d.f1 13071 165) d.f2 ≤
      ((4264389221 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4264389221 / 1000000000000000000)) * ((1422672523 / 1000000000000000000)) * (126 / 100) +
      2 * (((1422672523 / 1000000000000000000)) ^ 2 + 2 * ((4264389221 / 1000000000000000000)) * ((4274249 / 12500000000000000))) +
      6 * ((1422672523 / 1000000000000000000)) * ((4274249 / 12500000000000000)) * (126 / 100) + 8 * ((4274249 / 12500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13071 165) (d.f1 13071 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13071 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13071 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13071 165) (d.f1 13071 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13071 165) (d.w1 13071 165) (d.w2 13071 165)
  have hwexpr0 : 0 ≤ d.w0 13071 165 + d.w1 13071 165 * √(π / 2) +
      2 * d.w2 13071 165 + energyR16 13071 *
      radiusPolynomialRoot16 (d.w0 13071 165) (d.w1 13071 165) (d.w2 13071 165) := by
    positivity
  constructor
  · change (13071 : ℝ) ^ 8 * (mA 13071 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13071 165) (d.f1 13071 165) d.f2 + locationR16 13071 *
        radiusPolynomialRoot16 (d.f0 13071 165) (d.f1 13071 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13071 : ℝ) ^ 8 * (mA 13071 : ℝ) ^ 8 *
        ((((4264389221 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4264389221 / 1000000000000000000)) * ((1422672523 / 1000000000000000000)) * (126 / 100) +
          2 * (((1422672523 / 1000000000000000000)) ^ 2 + 2 * ((4264389221 / 1000000000000000000)) * ((4274249 / 12500000000000000))) +
          6 * ((1422672523 / 1000000000000000000)) * ((4274249 / 12500000000000000)) * (126 / 100) + 8 * ((4274249 / 12500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13071) *
          (32 * (((4264389221 / 1000000000000000000) : ℝ) + (1422672523 / 1000000000000000000) + (4274249 / 12500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13071 : ℝ) ^ 16 *
      (d.w0 13071 165 + d.w1 13071 165 * √(π / 2) + 2 * d.w2 13071 165 +
        energyR16 13071 * radiusPolynomialRoot16 (d.w0 13071 165) (d.w1 13071 165)
          (d.w2 13071 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13071 : ℝ) ^ 16 *
        (((1681482503 / 100000000000000000000) : ℝ) + ((598171371 / 50000000000000000000)) * (126 / 100) + 2 * ((54639127 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13071) *
          (32 * (((1681482503 / 100000000000000000000) : ℝ) + (598171371 / 50000000000000000000) + (54639127 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13071

/-! A coarse bound on the actual paper statistics constant at dimension 13072. -/
namespace BstLean.Part266.Row13072
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13070 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13070 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13070 128 ≤ (13324 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13324 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13072) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13072 : ℕ))
    (by norm_num : (13072 : ℕ) ≤ 16384)
  have ht : paperTail256 13072 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13072 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13072 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13072 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13072 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13072 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13070 128 * √(2 / (13072 : ℝ)) *
      (√(13072 : ℝ) + paperT0 13072 + paperTail256 13072) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13072 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13072 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13072 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13070 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13070 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13072 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13072

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13072
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13072 (61 / 100) 165 (17 / (100 * 13072)) (26 / (10 * 13072)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13072 (61 / 100) 165 (17 / (100 * 13072)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (43700877 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (267447231 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2028396577 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13072 / 13072 * (61 / 100)) ^ 4 * inverseRadius8 (13072 - 1) /
            envelopeGap 13072 (61 / 100) 165 (17 / (100 * 13072)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13072

namespace BstLean.Part266.Row13072
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13072 165 ≤ (4263573847 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13072 165 ≤ (1422400481 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (34187453 / 100000000000000000)
  w0 : (tableEnvelope C).w0 13072 165 ≤ (840548327 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13072 165 ≤ (74754263 / 6250000000000000000)
  w2 : (tableEnvelope C).w2 13072 165 ≤ (4370127 / 1000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (43700877 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (43700877 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (267447231 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2028396577 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((360623 / 100000000) : ℝ) ≤ √(17 / (100 * 13072) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13072) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2090475473 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4571029963 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13072) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13072) ≤ (108186473 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13072) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13072 * (165 : ℝ) ^ 2 + 26 / (10 * 13072) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13072) : ℝ)) (tA 13072 * 165 ^ 2 + 26 / (10 * 13072)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((360623 / 100000000))) * ((43700877 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((360623 / 100000000)) ^ 3) * ((267447231 / 200000000000000000000000))) + ((2028396577 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((360623 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13072) : ℝ)) d.D d.V d.P (√(tA 13072) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((360623 / 100000000)) ^ 2 * (((2090475473 / 1000000000000000)) * ((4571029963 / 125000000000000000)))) + ((2028396577 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13072) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((360623 / 100000000)) * ((43700877 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13072) : ℝ)) (tA 13072 * 165 ^ 2 + 26 / (10 * 13072)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((43700877 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((360623 / 100000000)) ^ 2) * ((267447231 / 200000000000000000000000)) + ((2028396577 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13072) : ℝ)) (√(26 / (10 * 13072) : ℝ)) d.D d.V d.P (√(tA 13072) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((360623 / 100000000)) * (((2090475473 / 1000000000000000)) * ((4571029963 / 125000000000000000))) + ((2028396577 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13072) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((43700877 / 10000000000000000000) : ℝ) + ((2028396577 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13072

namespace BstLean.Part266.Row13072
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13072 165 ∧
    0 ≤ (tableEnvelope C).f1 13072 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13072 165 ∧
    0 ≤ (tableEnvelope C).w1 13072 165 ∧ 0 ≤ (tableEnvelope C).w2 13072 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13072 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13072 165 ∧ 0 ≤ d.f1 13072 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13072 165 ∧ 0 ≤ d.w1 13072 165 ∧ 0 ≤ d.w2 13072 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13072 ≤ 2 * (228 / 100 : ℝ) / 13072 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13072 ≤ 2 * (370 / 100 : ℝ) / 13072 := by
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
    (completeRAData (tableEnvelope C) 13072 165).locationBound 13072 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13072 165).energyBound 13072 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13072 165) (d.f1 13072 165) d.f2 ≤
      32 * (((4263573847 / 1000000000000000000) : ℝ) + (1422400481 / 1000000000000000000) + (34187453 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13072 165) (d.w1 13072 165)
      (d.w2 13072 165) ≤
      32 * (((840548327 / 50000000000000000000) : ℝ) + (74754263 / 6250000000000000000) + (4370127 / 1000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13072 165) (d.f1 13072 165) d.f2 ≤
      ((4263573847 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4263573847 / 1000000000000000000)) * ((1422400481 / 1000000000000000000)) * (126 / 100) +
      2 * (((1422400481 / 1000000000000000000)) ^ 2 + 2 * ((4263573847 / 1000000000000000000)) * ((34187453 / 100000000000000000))) +
      6 * ((1422400481 / 1000000000000000000)) * ((34187453 / 100000000000000000)) * (126 / 100) + 8 * ((34187453 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13072 165) (d.f1 13072 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13072 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13072 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13072 165) (d.f1 13072 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13072 165) (d.w1 13072 165) (d.w2 13072 165)
  have hwexpr0 : 0 ≤ d.w0 13072 165 + d.w1 13072 165 * √(π / 2) +
      2 * d.w2 13072 165 + energyR16 13072 *
      radiusPolynomialRoot16 (d.w0 13072 165) (d.w1 13072 165) (d.w2 13072 165) := by
    positivity
  constructor
  · change (13072 : ℝ) ^ 8 * (mA 13072 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13072 165) (d.f1 13072 165) d.f2 + locationR16 13072 *
        radiusPolynomialRoot16 (d.f0 13072 165) (d.f1 13072 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13072 : ℝ) ^ 8 * (mA 13072 : ℝ) ^ 8 *
        ((((4263573847 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4263573847 / 1000000000000000000)) * ((1422400481 / 1000000000000000000)) * (126 / 100) +
          2 * (((1422400481 / 1000000000000000000)) ^ 2 + 2 * ((4263573847 / 1000000000000000000)) * ((34187453 / 100000000000000000))) +
          6 * ((1422400481 / 1000000000000000000)) * ((34187453 / 100000000000000000)) * (126 / 100) + 8 * ((34187453 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13072) *
          (32 * (((4263573847 / 1000000000000000000) : ℝ) + (1422400481 / 1000000000000000000) + (34187453 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13072 : ℝ) ^ 16 *
      (d.w0 13072 165 + d.w1 13072 165 * √(π / 2) + 2 * d.w2 13072 165 +
        energyR16 13072 * radiusPolynomialRoot16 (d.w0 13072 165) (d.w1 13072 165)
          (d.w2 13072 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13072 : ℝ) ^ 16 *
        (((840548327 / 50000000000000000000) : ℝ) + ((74754263 / 6250000000000000000)) * (126 / 100) + 2 * ((4370127 / 1000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13072) *
          (32 * (((840548327 / 50000000000000000000) : ℝ) + (74754263 / 6250000000000000000) + (4370127 / 1000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13072

/-! A coarse bound on the actual paper statistics constant at dimension 13073. -/
namespace BstLean.Part266.Row13073
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13071 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13071 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13071 128 ≤ (13325 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13325 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13073) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13073 : ℕ))
    (by norm_num : (13073 : ℕ) ≤ 16384)
  have ht : paperTail256 13073 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13073 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13073 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13073 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13073 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13073 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13071 128 * √(2 / (13073 : ℝ)) *
      (√(13073 : ℝ) + paperT0 13073 + paperTail256 13073) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13073 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13073 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13073 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13071 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13071 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13073 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13073

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13073
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13073 (61 / 100) 165 (17 / (100 * 13073)) (26 / (10 * 13073)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13073 (61 / 100) 165 (17 / (100 * 13073)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (436908487 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1336827027 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4054287899 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13073 / 13073 * (61 / 100)) ^ 4 * inverseRadius8 (13073 - 1) /
            envelopeGap 13073 (61 / 100) 165 (17 / (100 * 13073)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13073

namespace BstLean.Part266.Row13073
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13073 165 ≤ (2131379373 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13073 165 ≤ (355532131 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (170904579 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13073 165 ≤ (1680710933 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13073 165 ≤ (1195793763 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13073 165 ≤ (87382483 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (436908487 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (436908487 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1336827027 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4054287899 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((901523 / 250000000) : ℝ) ≤ √(17 / (100 * 13073) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13073) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1045117801 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36562645241 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13073) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13073) ≤ (108178197 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13073) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13073 * (165 : ℝ) ^ 2 + 26 / (10 * 13073) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13073) : ℝ)) (tA 13073 * 165 ^ 2 + 26 / (10 * 13073)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((901523 / 250000000))) * ((436908487 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((901523 / 250000000)) ^ 3) * ((1336827027 / 1000000000000000000000000))) + ((4054287899 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((901523 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13073) : ℝ)) d.D d.V d.P (√(tA 13073) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((901523 / 250000000)) ^ 2 * (((1045117801 / 500000000000000)) * ((36562645241 / 1000000000000000000)))) + ((4054287899 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13073) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((901523 / 250000000)) * ((436908487 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13073) : ℝ)) (tA 13073 * 165 ^ 2 + 26 / (10 * 13073)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((436908487 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((901523 / 250000000)) ^ 2) * ((1336827027 / 1000000000000000000000000)) + ((4054287899 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13073) : ℝ)) (√(26 / (10 * 13073) : ℝ)) d.D d.V d.P (√(tA 13073) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((901523 / 250000000)) * (((1045117801 / 500000000000000)) * ((36562645241 / 1000000000000000000))) + ((4054287899 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13073) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((436908487 / 100000000000000000000) : ℝ) + ((4054287899 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13073

namespace BstLean.Part266.Row13073
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13073 165 ∧
    0 ≤ (tableEnvelope C).f1 13073 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13073 165 ∧
    0 ≤ (tableEnvelope C).w1 13073 165 ∧ 0 ≤ (tableEnvelope C).w2 13073 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13073 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13073 165 ∧ 0 ≤ d.f1 13073 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13073 165 ∧ 0 ≤ d.w1 13073 165 ∧ 0 ≤ d.w2 13073 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13073 ≤ 2 * (228 / 100 : ℝ) / 13073 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13073 ≤ 2 * (370 / 100 : ℝ) / 13073 := by
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
    (completeRAData (tableEnvelope C) 13073 165).locationBound 13073 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13073 165).energyBound 13073 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13073 165) (d.f1 13073 165) d.f2 ≤
      32 * (((2131379373 / 500000000000000000) : ℝ) + (355532131 / 250000000000000000) + (170904579 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13073 165) (d.w1 13073 165)
      (d.w2 13073 165) ≤
      32 * (((1680710933 / 100000000000000000000) : ℝ) + (1195793763 / 100000000000000000000) + (87382483 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13073 165) (d.f1 13073 165) d.f2 ≤
      ((2131379373 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2131379373 / 500000000000000000)) * ((355532131 / 250000000000000000)) * (126 / 100) +
      2 * (((355532131 / 250000000000000000)) ^ 2 + 2 * ((2131379373 / 500000000000000000)) * ((170904579 / 500000000000000000))) +
      6 * ((355532131 / 250000000000000000)) * ((170904579 / 500000000000000000)) * (126 / 100) + 8 * ((170904579 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13073 165) (d.f1 13073 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13073 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13073 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13073 165) (d.f1 13073 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13073 165) (d.w1 13073 165) (d.w2 13073 165)
  have hwexpr0 : 0 ≤ d.w0 13073 165 + d.w1 13073 165 * √(π / 2) +
      2 * d.w2 13073 165 + energyR16 13073 *
      radiusPolynomialRoot16 (d.w0 13073 165) (d.w1 13073 165) (d.w2 13073 165) := by
    positivity
  constructor
  · change (13073 : ℝ) ^ 8 * (mA 13073 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13073 165) (d.f1 13073 165) d.f2 + locationR16 13073 *
        radiusPolynomialRoot16 (d.f0 13073 165) (d.f1 13073 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13073 : ℝ) ^ 8 * (mA 13073 : ℝ) ^ 8 *
        ((((2131379373 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2131379373 / 500000000000000000)) * ((355532131 / 250000000000000000)) * (126 / 100) +
          2 * (((355532131 / 250000000000000000)) ^ 2 + 2 * ((2131379373 / 500000000000000000)) * ((170904579 / 500000000000000000))) +
          6 * ((355532131 / 250000000000000000)) * ((170904579 / 500000000000000000)) * (126 / 100) + 8 * ((170904579 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13073) *
          (32 * (((2131379373 / 500000000000000000) : ℝ) + (355532131 / 250000000000000000) + (170904579 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13073 : ℝ) ^ 16 *
      (d.w0 13073 165 + d.w1 13073 165 * √(π / 2) + 2 * d.w2 13073 165 +
        energyR16 13073 * radiusPolynomialRoot16 (d.w0 13073 165) (d.w1 13073 165)
          (d.w2 13073 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13073 : ℝ) ^ 16 *
        (((1680710933 / 100000000000000000000) : ℝ) + ((1195793763 / 100000000000000000000)) * (126 / 100) + 2 * ((87382483 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13073) *
          (32 * (((1680710933 / 100000000000000000000) : ℝ) + (1195793763 / 100000000000000000000) + (87382483 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13073

/-! A coarse bound on the actual paper statistics constant at dimension 13074. -/
namespace BstLean.Part266.Row13074
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13072 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13072 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13072 128 ≤ (13326 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13326 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13074) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13074 : ℕ))
    (by norm_num : (13074 : ℕ) ≤ 16384)
  have ht : paperTail256 13074 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13074 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13074 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13074 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13074 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13074 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13072 128 * √(2 / (13074 : ℝ)) *
      (√(13074 : ℝ) + paperT0 13074 + paperTail256 13074) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13074 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13074 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13074 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13072 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13072 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13074 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13074

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13074
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13074 (61 / 100) 165 (17 / (100 * 13074)) (26 / (10 * 13074)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13074 (61 / 100) 165 (17 / (100 * 13074)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (87361647 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (267283611 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (810356877 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13074 / 13074 * (61 / 100)) ^ 4 * inverseRadius8 (13074 - 1) /
            envelopeGap 13074 (61 / 100) 165 (17 / (100 * 13074)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13074

namespace BstLean.Part266.Row13074
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13074 165 ≤ (1065485979 / 250000000000000000)
  f1 : (tableEnvelope C).f1 13074 165 ≤ (355464163 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (68348761 / 200000000000000000)
  w0 : (tableEnvelope C).w0 13074 165 ≤ (84016267 / 5000000000000000000)
  w1 : (tableEnvelope C).w1 13074 165 ≤ (74719963 / 6250000000000000000)
  w2 : (tableEnvelope C).w2 13074 165 ≤ (682519 / 156250000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (87361647 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (87361647 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (267283611 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (810356877 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1802977 / 500000000) : ℝ) ≤ √(17 / (100 * 13074) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13074) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1044997889 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4569631507 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13074) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13074) ≤ (108169923 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13074) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13074 * (165 : ℝ) ^ 2 + 26 / (10 * 13074) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13074) : ℝ)) (tA 13074 * 165 ^ 2 + 26 / (10 * 13074)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1802977 / 500000000))) * ((87361647 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1802977 / 500000000)) ^ 3) * ((267283611 / 200000000000000000000000))) + ((810356877 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1802977 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13074) : ℝ)) d.D d.V d.P (√(tA 13074) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1802977 / 500000000)) ^ 2 * (((1044997889 / 500000000000000)) * ((4569631507 / 125000000000000000)))) + ((810356877 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13074) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1802977 / 500000000)) * ((87361647 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13074) : ℝ)) (tA 13074 * 165 ^ 2 + 26 / (10 * 13074)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((87361647 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1802977 / 500000000)) ^ 2) * ((267283611 / 200000000000000000000000)) + ((810356877 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13074) : ℝ)) (√(26 / (10 * 13074) : ℝ)) d.D d.V d.P (√(tA 13074) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1802977 / 500000000)) * (((1044997889 / 500000000000000)) * ((4569631507 / 125000000000000000))) + ((810356877 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13074) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((87361647 / 20000000000000000000) : ℝ) + ((810356877 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13074

namespace BstLean.Part266.Row13074
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13074 165 ∧
    0 ≤ (tableEnvelope C).f1 13074 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13074 165 ∧
    0 ≤ (tableEnvelope C).w1 13074 165 ∧ 0 ≤ (tableEnvelope C).w2 13074 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13074 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13074 165 ∧ 0 ≤ d.f1 13074 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13074 165 ∧ 0 ≤ d.w1 13074 165 ∧ 0 ≤ d.w2 13074 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13074 ≤ 2 * (228 / 100 : ℝ) / 13074 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13074 ≤ 2 * (370 / 100 : ℝ) / 13074 := by
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
    (completeRAData (tableEnvelope C) 13074 165).locationBound 13074 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13074 165).energyBound 13074 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13074 165) (d.f1 13074 165) d.f2 ≤
      32 * (((1065485979 / 250000000000000000) : ℝ) + (355464163 / 250000000000000000) + (68348761 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13074 165) (d.w1 13074 165)
      (d.w2 13074 165) ≤
      32 * (((84016267 / 5000000000000000000) : ℝ) + (74719963 / 6250000000000000000) + (682519 / 156250000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13074 165) (d.f1 13074 165) d.f2 ≤
      ((1065485979 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1065485979 / 250000000000000000)) * ((355464163 / 250000000000000000)) * (126 / 100) +
      2 * (((355464163 / 250000000000000000)) ^ 2 + 2 * ((1065485979 / 250000000000000000)) * ((68348761 / 200000000000000000))) +
      6 * ((355464163 / 250000000000000000)) * ((68348761 / 200000000000000000)) * (126 / 100) + 8 * ((68348761 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13074 165) (d.f1 13074 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13074 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13074 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13074 165) (d.f1 13074 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13074 165) (d.w1 13074 165) (d.w2 13074 165)
  have hwexpr0 : 0 ≤ d.w0 13074 165 + d.w1 13074 165 * √(π / 2) +
      2 * d.w2 13074 165 + energyR16 13074 *
      radiusPolynomialRoot16 (d.w0 13074 165) (d.w1 13074 165) (d.w2 13074 165) := by
    positivity
  constructor
  · change (13074 : ℝ) ^ 8 * (mA 13074 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13074 165) (d.f1 13074 165) d.f2 + locationR16 13074 *
        radiusPolynomialRoot16 (d.f0 13074 165) (d.f1 13074 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13074 : ℝ) ^ 8 * (mA 13074 : ℝ) ^ 8 *
        ((((1065485979 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1065485979 / 250000000000000000)) * ((355464163 / 250000000000000000)) * (126 / 100) +
          2 * (((355464163 / 250000000000000000)) ^ 2 + 2 * ((1065485979 / 250000000000000000)) * ((68348761 / 200000000000000000))) +
          6 * ((355464163 / 250000000000000000)) * ((68348761 / 200000000000000000)) * (126 / 100) + 8 * ((68348761 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13074) *
          (32 * (((1065485979 / 250000000000000000) : ℝ) + (355464163 / 250000000000000000) + (68348761 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13074 : ℝ) ^ 16 *
      (d.w0 13074 165 + d.w1 13074 165 * √(π / 2) + 2 * d.w2 13074 165 +
        energyR16 13074 * radiusPolynomialRoot16 (d.w0 13074 165) (d.w1 13074 165)
          (d.w2 13074 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13074 : ℝ) ^ 16 *
        (((84016267 / 5000000000000000000) : ℝ) + ((74719963 / 6250000000000000000)) * (126 / 100) + 2 * ((682519 / 156250000000000000)) +
          (2 * (370 / 100 : ℝ) / 13074) *
          (32 * (((84016267 / 5000000000000000000) : ℝ) + (74719963 / 6250000000000000000) + (682519 / 156250000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13074
