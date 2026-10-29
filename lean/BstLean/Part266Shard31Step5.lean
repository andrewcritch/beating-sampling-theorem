import BstLean.Part266Shard31Step4


/-! A coarse bound on the actual paper statistics constant at dimension 13125. -/
namespace BstLean.Part266.Row13125
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13123 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13123 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13123 128 ≤ (13377 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13377 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13125) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13125 : ℕ))
    (by norm_num : (13125 : ℕ) ≤ 16384)
  have ht : paperTail256 13125 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13125 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13125 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13125 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13125 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13125 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13123 128 * √(2 / (13125 : ℝ)) *
      (√(13125 : ℝ) + paperT0 13125 + paperTail256 13125) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13125 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13125 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13125 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13123 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13123 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13125 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13125

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13125
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13125 (61 / 100) 165 (17 / (100 * 13125)) (26 / (10 * 13125)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13125 (61 / 100) 165 (17 / (100 * 13125)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (431735803 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (657883137 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3926384001 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13125 / 13125 * (61 / 100)) ^ 4 * inverseRadius8 (13125 - 1) /
            envelopeGap 13125 (61 / 100) 165 (17 / (100 * 13125)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13125

namespace BstLean.Part266.Row13125
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13125 165 ≤ (2110330673 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13125 165 ≤ (687541 / 488281250000000)
  f2 : (tableEnvelope C).f2 ≤ (338433507 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13125 165 ≤ (1660812781 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13125 165 ≤ (1181636543 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13125 165 ≤ (431739607 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (431735803 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (431735803 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (657883137 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3926384001 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3598941 / 1000000000) : ℝ) ≤ √(17 / (100 * 13125) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13125) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2077825313 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36273492719 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13125) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13125) ≤ (21549921 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13125) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13125 * (165 : ℝ) ^ 2 + 26 / (10 * 13125) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13125) : ℝ)) (tA 13125 * 165 ^ 2 + 26 / (10 * 13125)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3598941 / 1000000000))) * ((431735803 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3598941 / 1000000000)) ^ 3) * ((657883137 / 500000000000000000000000))) + ((3926384001 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3598941 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13125) : ℝ)) d.D d.V d.P (√(tA 13125) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3598941 / 1000000000)) ^ 2 * (((2077825313 / 1000000000000000)) * ((36273492719 / 1000000000000000000)))) + ((3926384001 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13125) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3598941 / 1000000000)) * ((431735803 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13125) : ℝ)) (tA 13125 * 165 ^ 2 + 26 / (10 * 13125)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((431735803 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3598941 / 1000000000)) ^ 2) * ((657883137 / 500000000000000000000000)) + ((3926384001 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13125) : ℝ)) (√(26 / (10 * 13125) : ℝ)) d.D d.V d.P (√(tA 13125) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3598941 / 1000000000)) * (((2077825313 / 1000000000000000)) * ((36273492719 / 1000000000000000000))) + ((3926384001 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13125) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((431735803 / 100000000000000000000) : ℝ) + ((3926384001 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13125

namespace BstLean.Part266.Row13125
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13125 165 ∧
    0 ≤ (tableEnvelope C).f1 13125 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13125 165 ∧
    0 ≤ (tableEnvelope C).w1 13125 165 ∧ 0 ≤ (tableEnvelope C).w2 13125 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13125 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13125 165 ∧ 0 ≤ d.f1 13125 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13125 165 ∧ 0 ≤ d.w1 13125 165 ∧ 0 ≤ d.w2 13125 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13125 ≤ 2 * (228 / 100 : ℝ) / 13125 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13125 ≤ 2 * (370 / 100 : ℝ) / 13125 := by
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
    (completeRAData (tableEnvelope C) 13125 165).locationBound 13125 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13125 165).energyBound 13125 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13125 165) (d.f1 13125 165) d.f2 ≤
      32 * (((2110330673 / 500000000000000000) : ℝ) + (687541 / 488281250000000) + (338433507 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13125 165) (d.w1 13125 165)
      (d.w2 13125 165) ≤
      32 * (((1660812781 / 100000000000000000000) : ℝ) + (1181636543 / 100000000000000000000) + (431739607 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13125 165) (d.f1 13125 165) d.f2 ≤
      ((2110330673 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2110330673 / 500000000000000000)) * ((687541 / 488281250000000)) * (126 / 100) +
      2 * (((687541 / 488281250000000)) ^ 2 + 2 * ((2110330673 / 500000000000000000)) * ((338433507 / 1000000000000000000))) +
      6 * ((687541 / 488281250000000)) * ((338433507 / 1000000000000000000)) * (126 / 100) + 8 * ((338433507 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13125 165) (d.f1 13125 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13125 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13125 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13125 165) (d.f1 13125 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13125 165) (d.w1 13125 165) (d.w2 13125 165)
  have hwexpr0 : 0 ≤ d.w0 13125 165 + d.w1 13125 165 * √(π / 2) +
      2 * d.w2 13125 165 + energyR16 13125 *
      radiusPolynomialRoot16 (d.w0 13125 165) (d.w1 13125 165) (d.w2 13125 165) := by
    positivity
  constructor
  · change (13125 : ℝ) ^ 8 * (mA 13125 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13125 165) (d.f1 13125 165) d.f2 + locationR16 13125 *
        radiusPolynomialRoot16 (d.f0 13125 165) (d.f1 13125 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13125 : ℝ) ^ 8 * (mA 13125 : ℝ) ^ 8 *
        ((((2110330673 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2110330673 / 500000000000000000)) * ((687541 / 488281250000000)) * (126 / 100) +
          2 * (((687541 / 488281250000000)) ^ 2 + 2 * ((2110330673 / 500000000000000000)) * ((338433507 / 1000000000000000000))) +
          6 * ((687541 / 488281250000000)) * ((338433507 / 1000000000000000000)) * (126 / 100) + 8 * ((338433507 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13125) *
          (32 * (((2110330673 / 500000000000000000) : ℝ) + (687541 / 488281250000000) + (338433507 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13125 : ℝ) ^ 16 *
      (d.w0 13125 165 + d.w1 13125 165 * √(π / 2) + 2 * d.w2 13125 165 +
        energyR16 13125 * radiusPolynomialRoot16 (d.w0 13125 165) (d.w1 13125 165)
          (d.w2 13125 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13125 : ℝ) ^ 16 *
        (((1660812781 / 100000000000000000000) : ℝ) + ((1181636543 / 100000000000000000000)) * (126 / 100) + 2 * ((431739607 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13125) *
          (32 * (((1660812781 / 100000000000000000000) : ℝ) + (1181636543 / 100000000000000000000) + (431739607 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13125

/-! A coarse bound on the actual paper statistics constant at dimension 13126. -/
namespace BstLean.Part266.Row13126
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13124 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13124 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13124 128 ≤ (13378 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13378 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13126) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13126 : ℕ))
    (by norm_num : (13126 : ℕ) ≤ 16384)
  have ht : paperTail256 13126 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13126 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13126 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13126 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13126 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13126 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13124 128 * √(2 / (13126 : ℝ)) *
      (√(13126 : ℝ) + paperT0 13126 + paperTail256 13126) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13126 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13126 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13126 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13124 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13124 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13126 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13126

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13126
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13126 (61 / 100) 165 (17 / (100 * 13126)) (26 / (10 * 13126)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13126 (61 / 100) 165 (17 / (100 * 13126)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (43163713 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (65768267 / 50000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3923969247 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13126 / 13126 * (61 / 100)) ^ 4 * inverseRadius8 (13126 - 1) /
            envelopeGap 13126 (61 / 100) 165 (17 / (100 * 13126)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13126

namespace BstLean.Part266.Row13126
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13126 165 ≤ (4219857149 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13126 165 ≤ (703907853 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (338369039 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13126 165 ≤ (83021657 / 5000000000000000000)
  w1 : (tableEnvelope C).w1 13126 165 ≤ (1181366451 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13126 165 ≤ (107910233 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (43163713 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (43163713 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (65768267 / 50000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3923969247 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((899701 / 250000000) : ℝ) ≤ √(17 / (100 * 13126) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13126) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2077587857 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7253593151 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13126) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13126) ≤ (26935349 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13126) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13126 * (165 : ℝ) ^ 2 + 26 / (10 * 13126) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13126) : ℝ)) (tA 13126 * 165 ^ 2 + 26 / (10 * 13126)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((899701 / 250000000))) * ((43163713 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((899701 / 250000000)) ^ 3) * ((65768267 / 50000000000000000000000))) + ((3923969247 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((899701 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13126) : ℝ)) d.D d.V d.P (√(tA 13126) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((899701 / 250000000)) ^ 2 * (((2077587857 / 1000000000000000)) * ((7253593151 / 200000000000000000)))) + ((3923969247 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13126) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((899701 / 250000000)) * ((43163713 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13126) : ℝ)) (tA 13126 * 165 ^ 2 + 26 / (10 * 13126)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((43163713 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((899701 / 250000000)) ^ 2) * ((65768267 / 50000000000000000000000)) + ((3923969247 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13126) : ℝ)) (√(26 / (10 * 13126) : ℝ)) d.D d.V d.P (√(tA 13126) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((899701 / 250000000)) * (((2077587857 / 1000000000000000)) * ((7253593151 / 200000000000000000))) + ((3923969247 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13126) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((43163713 / 10000000000000000000) : ℝ) + ((3923969247 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13126

namespace BstLean.Part266.Row13126
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13126 165 ∧
    0 ≤ (tableEnvelope C).f1 13126 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13126 165 ∧
    0 ≤ (tableEnvelope C).w1 13126 165 ∧ 0 ≤ (tableEnvelope C).w2 13126 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13126 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13126 165 ∧ 0 ≤ d.f1 13126 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13126 165 ∧ 0 ≤ d.w1 13126 165 ∧ 0 ≤ d.w2 13126 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13126 ≤ 2 * (228 / 100 : ℝ) / 13126 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13126 ≤ 2 * (370 / 100 : ℝ) / 13126 := by
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
    (completeRAData (tableEnvelope C) 13126 165).locationBound 13126 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13126 165).energyBound 13126 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13126 165) (d.f1 13126 165) d.f2 ≤
      32 * (((4219857149 / 1000000000000000000) : ℝ) + (703907853 / 500000000000000000) + (338369039 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13126 165) (d.w1 13126 165)
      (d.w2 13126 165) ≤
      32 * (((83021657 / 5000000000000000000) : ℝ) + (1181366451 / 100000000000000000000) + (107910233 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13126 165) (d.f1 13126 165) d.f2 ≤
      ((4219857149 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4219857149 / 1000000000000000000)) * ((703907853 / 500000000000000000)) * (126 / 100) +
      2 * (((703907853 / 500000000000000000)) ^ 2 + 2 * ((4219857149 / 1000000000000000000)) * ((338369039 / 1000000000000000000))) +
      6 * ((703907853 / 500000000000000000)) * ((338369039 / 1000000000000000000)) * (126 / 100) + 8 * ((338369039 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13126 165) (d.f1 13126 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13126 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13126 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13126 165) (d.f1 13126 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13126 165) (d.w1 13126 165) (d.w2 13126 165)
  have hwexpr0 : 0 ≤ d.w0 13126 165 + d.w1 13126 165 * √(π / 2) +
      2 * d.w2 13126 165 + energyR16 13126 *
      radiusPolynomialRoot16 (d.w0 13126 165) (d.w1 13126 165) (d.w2 13126 165) := by
    positivity
  constructor
  · change (13126 : ℝ) ^ 8 * (mA 13126 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13126 165) (d.f1 13126 165) d.f2 + locationR16 13126 *
        radiusPolynomialRoot16 (d.f0 13126 165) (d.f1 13126 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13126 : ℝ) ^ 8 * (mA 13126 : ℝ) ^ 8 *
        ((((4219857149 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4219857149 / 1000000000000000000)) * ((703907853 / 500000000000000000)) * (126 / 100) +
          2 * (((703907853 / 500000000000000000)) ^ 2 + 2 * ((4219857149 / 1000000000000000000)) * ((338369039 / 1000000000000000000))) +
          6 * ((703907853 / 500000000000000000)) * ((338369039 / 1000000000000000000)) * (126 / 100) + 8 * ((338369039 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13126) *
          (32 * (((4219857149 / 1000000000000000000) : ℝ) + (703907853 / 500000000000000000) + (338369039 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13126 : ℝ) ^ 16 *
      (d.w0 13126 165 + d.w1 13126 165 * √(π / 2) + 2 * d.w2 13126 165 +
        energyR16 13126 * radiusPolynomialRoot16 (d.w0 13126 165) (d.w1 13126 165)
          (d.w2 13126 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13126 : ℝ) ^ 16 *
        (((83021657 / 5000000000000000000) : ℝ) + ((1181366451 / 100000000000000000000)) * (126 / 100) + 2 * ((107910233 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13126) *
          (32 * (((83021657 / 5000000000000000000) : ℝ) + (1181366451 / 100000000000000000000) + (107910233 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13126

/-! A coarse bound on the actual paper statistics constant at dimension 13127. -/
namespace BstLean.Part266.Row13127
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13125 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13125 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13125 128 ≤ (13379 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13379 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13127) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13127 : ℕ))
    (by norm_num : (13127 : ℕ) ≤ 16384)
  have ht : paperTail256 13127 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13127 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13127 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13127 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13127 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13127 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13125 128 * √(2 / (13127 : ℝ)) *
      (√(13127 : ℝ) + paperT0 13127 + paperTail256 13127) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13127 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13127 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13127 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13125 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13125 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13127 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13127

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13127
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13127 (61 / 100) 165 (17 / (100 * 13127)) (26 / (10 * 13127)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13127 (61 / 100) 165 (17 / (100 * 13127)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (53942311 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (657482279 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (784311233 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13127 / 13127 * (61 / 100)) ^ 4 * inverseRadius8 (13127 - 1) /
            envelopeGap 13127 (61 / 100) 165 (17 / (100 * 13127)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13127

namespace BstLean.Part266.Row13127
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13127 165 ≤ (4219053217 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13127 165 ≤ (1407547529 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (33830459 / 100000000000000000)
  w0 : (tableEnvelope C).w0 13127 165 ≤ (830026813 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13127 165 ≤ (590548223 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13127 165 ≤ (431542287 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (53942311 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (53942311 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (657482279 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (784311233 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3598667 / 1000000000) : ℝ) ≤ √(17 / (100 * 13127) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13127) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (129834403 / 62500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7252488009 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13127) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13127) ≤ (107733189 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13127) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13127 * (165 : ℝ) ^ 2 + 26 / (10 * 13127) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13127) : ℝ)) (tA 13127 * 165 ^ 2 + 26 / (10 * 13127)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3598667 / 1000000000))) * ((53942311 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3598667 / 1000000000)) ^ 3) * ((657482279 / 500000000000000000000000))) + ((784311233 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3598667 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13127) : ℝ)) d.D d.V d.P (√(tA 13127) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3598667 / 1000000000)) ^ 2 * (((129834403 / 62500000000000)) * ((7252488009 / 200000000000000000)))) + ((784311233 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13127) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3598667 / 1000000000)) * ((53942311 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13127) : ℝ)) (tA 13127 * 165 ^ 2 + 26 / (10 * 13127)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((53942311 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3598667 / 1000000000)) ^ 2) * ((657482279 / 500000000000000000000000)) + ((784311233 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13127) : ℝ)) (√(26 / (10 * 13127) : ℝ)) d.D d.V d.P (√(tA 13127) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3598667 / 1000000000)) * (((129834403 / 62500000000000)) * ((7252488009 / 200000000000000000))) + ((784311233 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13127) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((53942311 / 12500000000000000000) : ℝ) + ((784311233 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13127

namespace BstLean.Part266.Row13127
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13127 165 ∧
    0 ≤ (tableEnvelope C).f1 13127 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13127 165 ∧
    0 ≤ (tableEnvelope C).w1 13127 165 ∧ 0 ≤ (tableEnvelope C).w2 13127 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13127 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13127 165 ∧ 0 ≤ d.f1 13127 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13127 165 ∧ 0 ≤ d.w1 13127 165 ∧ 0 ≤ d.w2 13127 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13127 ≤ 2 * (228 / 100 : ℝ) / 13127 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13127 ≤ 2 * (370 / 100 : ℝ) / 13127 := by
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
    (completeRAData (tableEnvelope C) 13127 165).locationBound 13127 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13127 165).energyBound 13127 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13127 165) (d.f1 13127 165) d.f2 ≤
      32 * (((4219053217 / 1000000000000000000) : ℝ) + (1407547529 / 1000000000000000000) + (33830459 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13127 165) (d.w1 13127 165)
      (d.w2 13127 165) ≤
      32 * (((830026813 / 50000000000000000000) : ℝ) + (590548223 / 50000000000000000000) + (431542287 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13127 165) (d.f1 13127 165) d.f2 ≤
      ((4219053217 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4219053217 / 1000000000000000000)) * ((1407547529 / 1000000000000000000)) * (126 / 100) +
      2 * (((1407547529 / 1000000000000000000)) ^ 2 + 2 * ((4219053217 / 1000000000000000000)) * ((33830459 / 100000000000000000))) +
      6 * ((1407547529 / 1000000000000000000)) * ((33830459 / 100000000000000000)) * (126 / 100) + 8 * ((33830459 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13127 165) (d.f1 13127 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13127 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13127 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13127 165) (d.f1 13127 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13127 165) (d.w1 13127 165) (d.w2 13127 165)
  have hwexpr0 : 0 ≤ d.w0 13127 165 + d.w1 13127 165 * √(π / 2) +
      2 * d.w2 13127 165 + energyR16 13127 *
      radiusPolynomialRoot16 (d.w0 13127 165) (d.w1 13127 165) (d.w2 13127 165) := by
    positivity
  constructor
  · change (13127 : ℝ) ^ 8 * (mA 13127 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13127 165) (d.f1 13127 165) d.f2 + locationR16 13127 *
        radiusPolynomialRoot16 (d.f0 13127 165) (d.f1 13127 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13127 : ℝ) ^ 8 * (mA 13127 : ℝ) ^ 8 *
        ((((4219053217 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4219053217 / 1000000000000000000)) * ((1407547529 / 1000000000000000000)) * (126 / 100) +
          2 * (((1407547529 / 1000000000000000000)) ^ 2 + 2 * ((4219053217 / 1000000000000000000)) * ((33830459 / 100000000000000000))) +
          6 * ((1407547529 / 1000000000000000000)) * ((33830459 / 100000000000000000)) * (126 / 100) + 8 * ((33830459 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13127) *
          (32 * (((4219053217 / 1000000000000000000) : ℝ) + (1407547529 / 1000000000000000000) + (33830459 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13127 : ℝ) ^ 16 *
      (d.w0 13127 165 + d.w1 13127 165 * √(π / 2) + 2 * d.w2 13127 165 +
        energyR16 13127 * radiusPolynomialRoot16 (d.w0 13127 165) (d.w1 13127 165)
          (d.w2 13127 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13127 : ℝ) ^ 16 *
        (((830026813 / 50000000000000000000) : ℝ) + ((590548223 / 50000000000000000000)) * (126 / 100) + 2 * ((431542287 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13127) *
          (32 * (((830026813 / 50000000000000000000) : ℝ) + (590548223 / 50000000000000000000) + (431542287 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13127

/-! A coarse bound on the actual paper statistics constant at dimension 13128. -/
namespace BstLean.Part266.Row13128
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13126 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13126 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13126 128 ≤ (13380 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13380 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13128) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13128 : ℕ))
    (by norm_num : (13128 : ℕ) ≤ 16384)
  have ht : paperTail256 13128 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13128 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13128 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13128 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13128 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13128 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13126 128 * √(2 / (13128 : ℝ)) *
      (√(13128 : ℝ) + paperT0 13128 + paperTail256 13128) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13128 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13128 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13128 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13126 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13126 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13128 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13128

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13128
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13128 (61 / 100) 165 (17 / (100 * 13128)) (26 / (10 * 13128)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13128 (61 / 100) 165 (17 / (100 * 13128)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (107859969 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1314563929 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1959572377 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13128 / 13128 * (61 / 100)) ^ 4 * inverseRadius8 (13128 - 1) /
            envelopeGap 13128 (61 / 100) 165 (17 / (100 * 13128)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13128

namespace BstLean.Part266.Row13128
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13128 165 ≤ (2109124777 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13128 165 ≤ (351819859 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (2114001 / 6250000000000000)
  w0 : (tableEnvelope C).w0 13128 165 ≤ (829837119 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13128 165 ≤ (1180826529 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13128 165 ≤ (431443673 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (107859969 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (107859969 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1314563929 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1959572377 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((359853 / 100000000) : ℝ) ≤ √(17 / (100 * 13128) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13128) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (519278271 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36256915603 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13128) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13128) ≤ (53862491 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13128) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13128 * (165 : ℝ) ^ 2 + 26 / (10 * 13128) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13128) : ℝ)) (tA 13128 * 165 ^ 2 + 26 / (10 * 13128)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((359853 / 100000000))) * ((107859969 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((359853 / 100000000)) ^ 3) * ((1314563929 / 1000000000000000000000000))) + ((1959572377 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((359853 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13128) : ℝ)) d.D d.V d.P (√(tA 13128) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((359853 / 100000000)) ^ 2 * (((519278271 / 250000000000000)) * ((36256915603 / 1000000000000000000)))) + ((1959572377 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13128) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((359853 / 100000000)) * ((107859969 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13128) : ℝ)) (tA 13128 * 165 ^ 2 + 26 / (10 * 13128)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((107859969 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((359853 / 100000000)) ^ 2) * ((1314563929 / 1000000000000000000000000)) + ((1959572377 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13128) : ℝ)) (√(26 / (10 * 13128) : ℝ)) d.D d.V d.P (√(tA 13128) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((359853 / 100000000)) * (((519278271 / 250000000000000)) * ((36256915603 / 1000000000000000000))) + ((1959572377 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13128) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((107859969 / 25000000000000000000) : ℝ) + ((1959572377 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13128

namespace BstLean.Part266.Row13128
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13128 165 ∧
    0 ≤ (tableEnvelope C).f1 13128 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13128 165 ∧
    0 ≤ (tableEnvelope C).w1 13128 165 ∧ 0 ≤ (tableEnvelope C).w2 13128 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13128 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13128 165 ∧ 0 ≤ d.f1 13128 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13128 165 ∧ 0 ≤ d.w1 13128 165 ∧ 0 ≤ d.w2 13128 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13128 ≤ 2 * (228 / 100 : ℝ) / 13128 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13128 ≤ 2 * (370 / 100 : ℝ) / 13128 := by
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
    (completeRAData (tableEnvelope C) 13128 165).locationBound 13128 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13128 165).energyBound 13128 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13128 165) (d.f1 13128 165) d.f2 ≤
      32 * (((2109124777 / 500000000000000000) : ℝ) + (351819859 / 250000000000000000) + (2114001 / 6250000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13128 165) (d.w1 13128 165)
      (d.w2 13128 165) ≤
      32 * (((829837119 / 50000000000000000000) : ℝ) + (1180826529 / 100000000000000000000) + (431443673 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13128 165) (d.f1 13128 165) d.f2 ≤
      ((2109124777 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2109124777 / 500000000000000000)) * ((351819859 / 250000000000000000)) * (126 / 100) +
      2 * (((351819859 / 250000000000000000)) ^ 2 + 2 * ((2109124777 / 500000000000000000)) * ((2114001 / 6250000000000000))) +
      6 * ((351819859 / 250000000000000000)) * ((2114001 / 6250000000000000)) * (126 / 100) + 8 * ((2114001 / 6250000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13128 165) (d.f1 13128 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13128 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13128 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13128 165) (d.f1 13128 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13128 165) (d.w1 13128 165) (d.w2 13128 165)
  have hwexpr0 : 0 ≤ d.w0 13128 165 + d.w1 13128 165 * √(π / 2) +
      2 * d.w2 13128 165 + energyR16 13128 *
      radiusPolynomialRoot16 (d.w0 13128 165) (d.w1 13128 165) (d.w2 13128 165) := by
    positivity
  constructor
  · change (13128 : ℝ) ^ 8 * (mA 13128 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13128 165) (d.f1 13128 165) d.f2 + locationR16 13128 *
        radiusPolynomialRoot16 (d.f0 13128 165) (d.f1 13128 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13128 : ℝ) ^ 8 * (mA 13128 : ℝ) ^ 8 *
        ((((2109124777 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2109124777 / 500000000000000000)) * ((351819859 / 250000000000000000)) * (126 / 100) +
          2 * (((351819859 / 250000000000000000)) ^ 2 + 2 * ((2109124777 / 500000000000000000)) * ((2114001 / 6250000000000000))) +
          6 * ((351819859 / 250000000000000000)) * ((2114001 / 6250000000000000)) * (126 / 100) + 8 * ((2114001 / 6250000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13128) *
          (32 * (((2109124777 / 500000000000000000) : ℝ) + (351819859 / 250000000000000000) + (2114001 / 6250000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13128 : ℝ) ^ 16 *
      (d.w0 13128 165 + d.w1 13128 165 * √(π / 2) + 2 * d.w2 13128 165 +
        energyR16 13128 * radiusPolynomialRoot16 (d.w0 13128 165) (d.w1 13128 165)
          (d.w2 13128 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13128 : ℝ) ^ 16 *
        (((829837119 / 50000000000000000000) : ℝ) + ((1180826529 / 100000000000000000000)) * (126 / 100) + 2 * ((431443673 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13128) *
          (32 * (((829837119 / 50000000000000000000) : ℝ) + (1180826529 / 100000000000000000000) + (431443673 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13128

/-! A coarse bound on the actual paper statistics constant at dimension 13129. -/
namespace BstLean.Part266.Row13129
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13127 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13127 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13127 128 ≤ (13381 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13381 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13129) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13129 : ℕ))
    (by norm_num : (13129 : ℕ) ≤ 16384)
  have ht : paperTail256 13129 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13129 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13129 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13129 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13129 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13129 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13127 128 * √(2 / (13129 : ℝ)) *
      (√(13129 : ℝ) + paperT0 13129 + paperTail256 13129) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13129 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13129 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13129 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13127 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13127 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13129 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13129

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13129
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13129 (61 / 100) 165 (17 / (100 * 13129)) (26 / (10 * 13129)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13129 (61 / 100) 165 (17 / (100 * 13129)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (431341293 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (328540863 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3916735013 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13129 / 13129 * (61 / 100)) ^ 4 * inverseRadius8 (13129 - 1) /
            envelopeGap 13129 (61 / 100) 165 (17 / (100 * 13129)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13129

namespace BstLean.Part266.Row13129
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13129 165 ≤ (4217446157 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13129 165 ≤ (43969107 / 31250000000000000)
  f2 : (tableEnvelope C).f2 ≤ (338175747 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13129 165 ≤ (66371799 / 4000000000000000000)
  w1 : (tableEnvelope C).w1 13129 165 ≤ (590278349 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13129 165 ≤ (6739767 / 1562500000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (431341293 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (431341293 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (328540863 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3916735013 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3598393 / 1000000000) : ℝ) ≤ √(17 / (100 * 13129) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13129) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1038437881 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7250278483 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13129) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13129) ≤ (107716777 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13129) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13129 * (165 : ℝ) ^ 2 + 26 / (10 * 13129) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13129) : ℝ)) (tA 13129 * 165 ^ 2 + 26 / (10 * 13129)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3598393 / 1000000000))) * ((431341293 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3598393 / 1000000000)) ^ 3) * ((328540863 / 250000000000000000000000))) + ((3916735013 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3598393 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13129) : ℝ)) d.D d.V d.P (√(tA 13129) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3598393 / 1000000000)) ^ 2 * (((1038437881 / 500000000000000)) * ((7250278483 / 200000000000000000)))) + ((3916735013 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13129) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3598393 / 1000000000)) * ((431341293 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13129) : ℝ)) (tA 13129 * 165 ^ 2 + 26 / (10 * 13129)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((431341293 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3598393 / 1000000000)) ^ 2) * ((328540863 / 250000000000000000000000)) + ((3916735013 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13129) : ℝ)) (√(26 / (10 * 13129) : ℝ)) d.D d.V d.P (√(tA 13129) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3598393 / 1000000000)) * (((1038437881 / 500000000000000)) * ((7250278483 / 200000000000000000))) + ((3916735013 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13129) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((431341293 / 100000000000000000000) : ℝ) + ((3916735013 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13129

namespace BstLean.Part266.Row13129
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13129 165 ∧
    0 ≤ (tableEnvelope C).f1 13129 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13129 165 ∧
    0 ≤ (tableEnvelope C).w1 13129 165 ∧ 0 ≤ (tableEnvelope C).w2 13129 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13129 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13129 165 ∧ 0 ≤ d.f1 13129 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13129 165 ∧ 0 ≤ d.w1 13129 165 ∧ 0 ≤ d.w2 13129 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13129 ≤ 2 * (228 / 100 : ℝ) / 13129 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13129 ≤ 2 * (370 / 100 : ℝ) / 13129 := by
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
    (completeRAData (tableEnvelope C) 13129 165).locationBound 13129 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13129 165).energyBound 13129 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13129 165) (d.f1 13129 165) d.f2 ≤
      32 * (((4217446157 / 1000000000000000000) : ℝ) + (43969107 / 31250000000000000) + (338175747 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13129 165) (d.w1 13129 165)
      (d.w2 13129 165) ≤
      32 * (((66371799 / 4000000000000000000) : ℝ) + (590278349 / 50000000000000000000) + (6739767 / 1562500000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13129 165) (d.f1 13129 165) d.f2 ≤
      ((4217446157 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4217446157 / 1000000000000000000)) * ((43969107 / 31250000000000000)) * (126 / 100) +
      2 * (((43969107 / 31250000000000000)) ^ 2 + 2 * ((4217446157 / 1000000000000000000)) * ((338175747 / 1000000000000000000))) +
      6 * ((43969107 / 31250000000000000)) * ((338175747 / 1000000000000000000)) * (126 / 100) + 8 * ((338175747 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13129 165) (d.f1 13129 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13129 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13129 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13129 165) (d.f1 13129 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13129 165) (d.w1 13129 165) (d.w2 13129 165)
  have hwexpr0 : 0 ≤ d.w0 13129 165 + d.w1 13129 165 * √(π / 2) +
      2 * d.w2 13129 165 + energyR16 13129 *
      radiusPolynomialRoot16 (d.w0 13129 165) (d.w1 13129 165) (d.w2 13129 165) := by
    positivity
  constructor
  · change (13129 : ℝ) ^ 8 * (mA 13129 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13129 165) (d.f1 13129 165) d.f2 + locationR16 13129 *
        radiusPolynomialRoot16 (d.f0 13129 165) (d.f1 13129 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13129 : ℝ) ^ 8 * (mA 13129 : ℝ) ^ 8 *
        ((((4217446157 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4217446157 / 1000000000000000000)) * ((43969107 / 31250000000000000)) * (126 / 100) +
          2 * (((43969107 / 31250000000000000)) ^ 2 + 2 * ((4217446157 / 1000000000000000000)) * ((338175747 / 1000000000000000000))) +
          6 * ((43969107 / 31250000000000000)) * ((338175747 / 1000000000000000000)) * (126 / 100) + 8 * ((338175747 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13129) *
          (32 * (((4217446157 / 1000000000000000000) : ℝ) + (43969107 / 31250000000000000) + (338175747 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13129 : ℝ) ^ 16 *
      (d.w0 13129 165 + d.w1 13129 165 * √(π / 2) + 2 * d.w2 13129 165 +
        energyR16 13129 * radiusPolynomialRoot16 (d.w0 13129 165) (d.w1 13129 165)
          (d.w2 13129 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13129 : ℝ) ^ 16 *
        (((66371799 / 4000000000000000000) : ℝ) + ((590278349 / 50000000000000000000)) * (126 / 100) + 2 * ((6739767 / 1562500000000000000)) +
          (2 * (370 / 100 : ℝ) / 13129) *
          (32 * (((66371799 / 4000000000000000000) : ℝ) + (590278349 / 50000000000000000000) + (6739767 / 1562500000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13129

/-! A coarse bound on the actual paper statistics constant at dimension 13130. -/
namespace BstLean.Part266.Row13130
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13128 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13128 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13128 128 ≤ (13382 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13382 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13130) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13130 : ℕ))
    (by norm_num : (13130 : ℕ) ≤ 16384)
  have ht : paperTail256 13130 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13130 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13130 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13130 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13130 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13130 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13128 128 * √(2 / (13130 : ℝ)) *
      (√(13130 : ℝ) + paperT0 13130 + paperTail256 13130) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13130 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13130 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13130 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13128 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13128 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13130 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13130

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13130
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13130 (61 / 100) 165 (17 / (100 * 13130)) (26 / (10 * 13130)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13130 (61 / 100) 165 (17 / (100 * 13130)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (431242741 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1313763129 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3914326941 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13130 / 13130 * (61 / 100)) ^ 4 * inverseRadius8 (13130 - 1) /
            envelopeGap 13130 (61 / 100) 165 (17 / (100 * 13130)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13130

namespace BstLean.Part266.Row13130
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13130 165 ≤ (4216643031 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13130 165 ≤ (1406743499 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (169055677 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13130 165 ≤ (324007 / 19531250000000000)
  w1 : (tableEnvelope C).w1 13130 165 ≤ (295071739 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 13130 165 ≤ (431246533 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (431242741 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (431242741 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1313763129 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3914326941 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((224891 / 62500000) : ℝ) ≤ √(17 / (100 * 13130) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13130) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2076638489 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3624587051 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13130) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13130) ≤ (107708573 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13130) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13130 * (165 : ℝ) ^ 2 + 26 / (10 * 13130) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13130) : ℝ)) (tA 13130 * 165 ^ 2 + 26 / (10 * 13130)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((224891 / 62500000))) * ((431242741 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((224891 / 62500000)) ^ 3) * ((1313763129 / 1000000000000000000000000))) + ((3914326941 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((224891 / 62500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13130) : ℝ)) d.D d.V d.P (√(tA 13130) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((224891 / 62500000)) ^ 2 * (((2076638489 / 1000000000000000)) * ((3624587051 / 100000000000000000)))) + ((3914326941 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13130) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((224891 / 62500000)) * ((431242741 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13130) : ℝ)) (tA 13130 * 165 ^ 2 + 26 / (10 * 13130)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((431242741 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((224891 / 62500000)) ^ 2) * ((1313763129 / 1000000000000000000000000)) + ((3914326941 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13130) : ℝ)) (√(26 / (10 * 13130) : ℝ)) d.D d.V d.P (√(tA 13130) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((224891 / 62500000)) * (((2076638489 / 1000000000000000)) * ((3624587051 / 100000000000000000))) + ((3914326941 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13130) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((431242741 / 100000000000000000000) : ℝ) + ((3914326941 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13130

namespace BstLean.Part266.Row13130
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13130 165 ∧
    0 ≤ (tableEnvelope C).f1 13130 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13130 165 ∧
    0 ≤ (tableEnvelope C).w1 13130 165 ∧ 0 ≤ (tableEnvelope C).w2 13130 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13130 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13130 165 ∧ 0 ≤ d.f1 13130 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13130 165 ∧ 0 ≤ d.w1 13130 165 ∧ 0 ≤ d.w2 13130 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13130 ≤ 2 * (228 / 100 : ℝ) / 13130 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13130 ≤ 2 * (370 / 100 : ℝ) / 13130 := by
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
    (completeRAData (tableEnvelope C) 13130 165).locationBound 13130 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13130 165).energyBound 13130 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13130 165) (d.f1 13130 165) d.f2 ≤
      32 * (((4216643031 / 1000000000000000000) : ℝ) + (1406743499 / 1000000000000000000) + (169055677 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13130 165) (d.w1 13130 165)
      (d.w2 13130 165) ≤
      32 * (((324007 / 19531250000000000) : ℝ) + (295071739 / 25000000000000000000) + (431246533 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13130 165) (d.f1 13130 165) d.f2 ≤
      ((4216643031 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4216643031 / 1000000000000000000)) * ((1406743499 / 1000000000000000000)) * (126 / 100) +
      2 * (((1406743499 / 1000000000000000000)) ^ 2 + 2 * ((4216643031 / 1000000000000000000)) * ((169055677 / 500000000000000000))) +
      6 * ((1406743499 / 1000000000000000000)) * ((169055677 / 500000000000000000)) * (126 / 100) + 8 * ((169055677 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13130 165) (d.f1 13130 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13130 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13130 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13130 165) (d.f1 13130 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13130 165) (d.w1 13130 165) (d.w2 13130 165)
  have hwexpr0 : 0 ≤ d.w0 13130 165 + d.w1 13130 165 * √(π / 2) +
      2 * d.w2 13130 165 + energyR16 13130 *
      radiusPolynomialRoot16 (d.w0 13130 165) (d.w1 13130 165) (d.w2 13130 165) := by
    positivity
  constructor
  · change (13130 : ℝ) ^ 8 * (mA 13130 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13130 165) (d.f1 13130 165) d.f2 + locationR16 13130 *
        radiusPolynomialRoot16 (d.f0 13130 165) (d.f1 13130 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13130 : ℝ) ^ 8 * (mA 13130 : ℝ) ^ 8 *
        ((((4216643031 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4216643031 / 1000000000000000000)) * ((1406743499 / 1000000000000000000)) * (126 / 100) +
          2 * (((1406743499 / 1000000000000000000)) ^ 2 + 2 * ((4216643031 / 1000000000000000000)) * ((169055677 / 500000000000000000))) +
          6 * ((1406743499 / 1000000000000000000)) * ((169055677 / 500000000000000000)) * (126 / 100) + 8 * ((169055677 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13130) *
          (32 * (((4216643031 / 1000000000000000000) : ℝ) + (1406743499 / 1000000000000000000) + (169055677 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13130 : ℝ) ^ 16 *
      (d.w0 13130 165 + d.w1 13130 165 * √(π / 2) + 2 * d.w2 13130 165 +
        energyR16 13130 * radiusPolynomialRoot16 (d.w0 13130 165) (d.w1 13130 165)
          (d.w2 13130 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13130 : ℝ) ^ 16 *
        (((324007 / 19531250000000000) : ℝ) + ((295071739 / 25000000000000000000)) * (126 / 100) + 2 * ((431246533 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13130) *
          (32 * (((324007 / 19531250000000000) : ℝ) + (295071739 / 25000000000000000000) + (431246533 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13130

/-! A coarse bound on the actual paper statistics constant at dimension 13131. -/
namespace BstLean.Part266.Row13131
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13129 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13129 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13129 128 ≤ (13383 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13383 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13131) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13131 : ℕ))
    (by norm_num : (13131 : ℕ) ≤ 16384)
  have ht : paperTail256 13131 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13131 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13131 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13131 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13131 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13131 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13129 128 * √(2 / (13131 : ℝ)) *
      (√(13131 : ℝ) + paperT0 13131 + paperTail256 13131) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13131 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13131 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13131 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13129 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13129 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13131 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13131

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13131
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13131 (61 / 100) 165 (17 / (100 * 13131)) (26 / (10 * 13131)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13131 (61 / 100) 165 (17 / (100 * 13131)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (431144219 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1313362957 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (782384107 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13131 / 13131 * (61 / 100)) ^ 4 * inverseRadius8 (13131 - 1) /
            envelopeGap 13131 (61 / 100) 165 (17 / (100 * 13131)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13131

namespace BstLean.Part266.Row13131
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13131 165 ≤ (526980021 / 125000000000000000)
  f1 : (tableEnvelope C).f1 13131 165 ≤ (175809457 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (16902349 / 50000000000000000)
  w0 : (tableEnvelope C).w0 13131 165 ≤ (1658536831 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13131 165 ≤ (1180017301 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13131 165 ≤ (431148009 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (431144219 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (431144219 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1313362957 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (782384107 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3598119 / 1000000000) : ℝ) ≤ √(17 / (100 * 13131) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13131) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (103820063 / 50000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36240349847 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13131) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13131) ≤ (107700371 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13131) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13131 * (165 : ℝ) ^ 2 + 26 / (10 * 13131) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13131) : ℝ)) (tA 13131 * 165 ^ 2 + 26 / (10 * 13131)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3598119 / 1000000000))) * ((431144219 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3598119 / 1000000000)) ^ 3) * ((1313362957 / 1000000000000000000000000))) + ((782384107 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3598119 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13131) : ℝ)) d.D d.V d.P (√(tA 13131) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3598119 / 1000000000)) ^ 2 * (((103820063 / 50000000000000)) * ((36240349847 / 1000000000000000000)))) + ((782384107 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13131) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3598119 / 1000000000)) * ((431144219 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13131) : ℝ)) (tA 13131 * 165 ^ 2 + 26 / (10 * 13131)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((431144219 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3598119 / 1000000000)) ^ 2) * ((1313362957 / 1000000000000000000000000)) + ((782384107 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13131) : ℝ)) (√(26 / (10 * 13131) : ℝ)) d.D d.V d.P (√(tA 13131) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3598119 / 1000000000)) * (((103820063 / 50000000000000)) * ((36240349847 / 1000000000000000000))) + ((782384107 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13131) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((431144219 / 100000000000000000000) : ℝ) + ((782384107 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13131

namespace BstLean.Part266.Row13131
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13131 165 ∧
    0 ≤ (tableEnvelope C).f1 13131 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13131 165 ∧
    0 ≤ (tableEnvelope C).w1 13131 165 ∧ 0 ≤ (tableEnvelope C).w2 13131 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13131 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13131 165 ∧ 0 ≤ d.f1 13131 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13131 165 ∧ 0 ≤ d.w1 13131 165 ∧ 0 ≤ d.w2 13131 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13131 ≤ 2 * (228 / 100 : ℝ) / 13131 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13131 ≤ 2 * (370 / 100 : ℝ) / 13131 := by
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
    (completeRAData (tableEnvelope C) 13131 165).locationBound 13131 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13131 165).energyBound 13131 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13131 165) (d.f1 13131 165) d.f2 ≤
      32 * (((526980021 / 125000000000000000) : ℝ) + (175809457 / 125000000000000000) + (16902349 / 50000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13131 165) (d.w1 13131 165)
      (d.w2 13131 165) ≤
      32 * (((1658536831 / 100000000000000000000) : ℝ) + (1180017301 / 100000000000000000000) + (431148009 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13131 165) (d.f1 13131 165) d.f2 ≤
      ((526980021 / 125000000000000000) : ℝ) ^ 2 + 2 * ((526980021 / 125000000000000000)) * ((175809457 / 125000000000000000)) * (126 / 100) +
      2 * (((175809457 / 125000000000000000)) ^ 2 + 2 * ((526980021 / 125000000000000000)) * ((16902349 / 50000000000000000))) +
      6 * ((175809457 / 125000000000000000)) * ((16902349 / 50000000000000000)) * (126 / 100) + 8 * ((16902349 / 50000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13131 165) (d.f1 13131 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13131 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13131 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13131 165) (d.f1 13131 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13131 165) (d.w1 13131 165) (d.w2 13131 165)
  have hwexpr0 : 0 ≤ d.w0 13131 165 + d.w1 13131 165 * √(π / 2) +
      2 * d.w2 13131 165 + energyR16 13131 *
      radiusPolynomialRoot16 (d.w0 13131 165) (d.w1 13131 165) (d.w2 13131 165) := by
    positivity
  constructor
  · change (13131 : ℝ) ^ 8 * (mA 13131 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13131 165) (d.f1 13131 165) d.f2 + locationR16 13131 *
        radiusPolynomialRoot16 (d.f0 13131 165) (d.f1 13131 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13131 : ℝ) ^ 8 * (mA 13131 : ℝ) ^ 8 *
        ((((526980021 / 125000000000000000) : ℝ) ^ 2 + 2 * ((526980021 / 125000000000000000)) * ((175809457 / 125000000000000000)) * (126 / 100) +
          2 * (((175809457 / 125000000000000000)) ^ 2 + 2 * ((526980021 / 125000000000000000)) * ((16902349 / 50000000000000000))) +
          6 * ((175809457 / 125000000000000000)) * ((16902349 / 50000000000000000)) * (126 / 100) + 8 * ((16902349 / 50000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13131) *
          (32 * (((526980021 / 125000000000000000) : ℝ) + (175809457 / 125000000000000000) + (16902349 / 50000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13131 : ℝ) ^ 16 *
      (d.w0 13131 165 + d.w1 13131 165 * √(π / 2) + 2 * d.w2 13131 165 +
        energyR16 13131 * radiusPolynomialRoot16 (d.w0 13131 165) (d.w1 13131 165)
          (d.w2 13131 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13131 : ℝ) ^ 16 *
        (((1658536831 / 100000000000000000000) : ℝ) + ((1180017301 / 100000000000000000000)) * (126 / 100) + 2 * ((431148009 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13131) *
          (32 * (((1658536831 / 100000000000000000000) : ℝ) + (1180017301 / 100000000000000000000) + (431148009 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13131

/-! A coarse bound on the actual paper statistics constant at dimension 13132. -/
namespace BstLean.Part266.Row13132
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13130 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13130 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13130 128 ≤ (13384 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13384 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13132) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13132 : ℕ))
    (by norm_num : (13132 : ℕ) ≤ 16384)
  have ht : paperTail256 13132 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13132 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13132 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13132 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13132 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13132 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13130 128 * √(2 / (13132 : ℝ)) *
      (√(13132 : ℝ) + paperT0 13132 + paperTail256 13132) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13132 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13132 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13132 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13130 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13130 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13132 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13132

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13132
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13132 (61 / 100) 165 (17 / (100 * 13132)) (26 / (10 * 13132)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13132 (61 / 100) 165 (17 / (100 * 13132)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (431045727 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (656481469 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (781903159 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13132 / 13132 * (61 / 100)) ^ 4 * inverseRadius8 (13132 - 1) /
            envelopeGap 13132 (61 / 100) 165 (17 / (100 * 13132)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13132

namespace BstLean.Part266.Row13132
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13132 165 ≤ (2107518787 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13132 165 ≤ (1406207897 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (10561957 / 31250000000000000)
  w0 : (tableEnvelope C).w0 13132 165 ≤ (414539487 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 13132 165 ≤ (1179747733 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13132 165 ≤ (86209903 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (431045727 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (431045727 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (656481469 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (781903159 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1798991 / 500000000) : ℝ) ≤ √(17 / (100 * 13132) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13132) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (519041019 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18117415227 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13132) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13132) ≤ (107692169 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13132) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13132 * (165 : ℝ) ^ 2 + 26 / (10 * 13132) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13132) : ℝ)) (tA 13132 * 165 ^ 2 + 26 / (10 * 13132)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1798991 / 500000000))) * ((431045727 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1798991 / 500000000)) ^ 3) * ((656481469 / 500000000000000000000000))) + ((781903159 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1798991 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13132) : ℝ)) d.D d.V d.P (√(tA 13132) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1798991 / 500000000)) ^ 2 * (((519041019 / 250000000000000)) * ((18117415227 / 500000000000000000)))) + ((781903159 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13132) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1798991 / 500000000)) * ((431045727 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13132) : ℝ)) (tA 13132 * 165 ^ 2 + 26 / (10 * 13132)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((431045727 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1798991 / 500000000)) ^ 2) * ((656481469 / 500000000000000000000000)) + ((781903159 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13132) : ℝ)) (√(26 / (10 * 13132) : ℝ)) d.D d.V d.P (√(tA 13132) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1798991 / 500000000)) * (((519041019 / 250000000000000)) * ((18117415227 / 500000000000000000))) + ((781903159 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13132) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((431045727 / 100000000000000000000) : ℝ) + ((781903159 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13132

namespace BstLean.Part266.Row13132
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13132 165 ∧
    0 ≤ (tableEnvelope C).f1 13132 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13132 165 ∧
    0 ≤ (tableEnvelope C).w1 13132 165 ∧ 0 ≤ (tableEnvelope C).w2 13132 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13132 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13132 165 ∧ 0 ≤ d.f1 13132 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13132 165 ∧ 0 ≤ d.w1 13132 165 ∧ 0 ≤ d.w2 13132 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13132 ≤ 2 * (228 / 100 : ℝ) / 13132 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13132 ≤ 2 * (370 / 100 : ℝ) / 13132 := by
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
    (completeRAData (tableEnvelope C) 13132 165).locationBound 13132 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13132 165).energyBound 13132 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13132 165) (d.f1 13132 165) d.f2 ≤
      32 * (((2107518787 / 500000000000000000) : ℝ) + (1406207897 / 1000000000000000000) + (10561957 / 31250000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13132 165) (d.w1 13132 165)
      (d.w2 13132 165) ≤
      32 * (((414539487 / 25000000000000000000) : ℝ) + (1179747733 / 100000000000000000000) + (86209903 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13132 165) (d.f1 13132 165) d.f2 ≤
      ((2107518787 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2107518787 / 500000000000000000)) * ((1406207897 / 1000000000000000000)) * (126 / 100) +
      2 * (((1406207897 / 1000000000000000000)) ^ 2 + 2 * ((2107518787 / 500000000000000000)) * ((10561957 / 31250000000000000))) +
      6 * ((1406207897 / 1000000000000000000)) * ((10561957 / 31250000000000000)) * (126 / 100) + 8 * ((10561957 / 31250000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13132 165) (d.f1 13132 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13132 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13132 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13132 165) (d.f1 13132 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13132 165) (d.w1 13132 165) (d.w2 13132 165)
  have hwexpr0 : 0 ≤ d.w0 13132 165 + d.w1 13132 165 * √(π / 2) +
      2 * d.w2 13132 165 + energyR16 13132 *
      radiusPolynomialRoot16 (d.w0 13132 165) (d.w1 13132 165) (d.w2 13132 165) := by
    positivity
  constructor
  · change (13132 : ℝ) ^ 8 * (mA 13132 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13132 165) (d.f1 13132 165) d.f2 + locationR16 13132 *
        radiusPolynomialRoot16 (d.f0 13132 165) (d.f1 13132 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13132 : ℝ) ^ 8 * (mA 13132 : ℝ) ^ 8 *
        ((((2107518787 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2107518787 / 500000000000000000)) * ((1406207897 / 1000000000000000000)) * (126 / 100) +
          2 * (((1406207897 / 1000000000000000000)) ^ 2 + 2 * ((2107518787 / 500000000000000000)) * ((10561957 / 31250000000000000))) +
          6 * ((1406207897 / 1000000000000000000)) * ((10561957 / 31250000000000000)) * (126 / 100) + 8 * ((10561957 / 31250000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13132) *
          (32 * (((2107518787 / 500000000000000000) : ℝ) + (1406207897 / 1000000000000000000) + (10561957 / 31250000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13132 : ℝ) ^ 16 *
      (d.w0 13132 165 + d.w1 13132 165 * √(π / 2) + 2 * d.w2 13132 165 +
        energyR16 13132 * radiusPolynomialRoot16 (d.w0 13132 165) (d.w1 13132 165)
          (d.w2 13132 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13132 : ℝ) ^ 16 *
        (((414539487 / 25000000000000000000) : ℝ) + ((1179747733 / 100000000000000000000)) * (126 / 100) + 2 * ((86209903 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13132) *
          (32 * (((414539487 / 25000000000000000000) : ℝ) + (1179747733 / 100000000000000000000) + (86209903 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13132

/-! A coarse bound on the actual paper statistics constant at dimension 13133. -/
namespace BstLean.Part266.Row13133
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13131 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13131 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13131 128 ≤ (13385 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13385 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13133) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13133 : ℕ))
    (by norm_num : (13133 : ℕ) ≤ 16384)
  have ht : paperTail256 13133 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13133 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13133 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13133 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13133 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13133 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13131 128 * √(2 / (13133 : ℝ)) *
      (√(13133 : ℝ) + paperT0 13133 + paperTail256 13133) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13133 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13133 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13133 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13131 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13131 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13133 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13133

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13133
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13133 (61 / 100) 165 (17 / (100 * 13133)) (26 / (10 * 13133)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13133 (61 / 100) 165 (17 / (100 * 13133)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (86189453 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1312563071 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (48838909 / 12500000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13133 / 13133 * (61 / 100)) ^ 4 * inverseRadius8 (13133 - 1) /
            envelopeGap 13133 (61 / 100) 165 (17 / (100 * 13133)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13133

namespace BstLean.Part266.Row13133
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13133 165 ≤ (842847049 / 200000000000000000)
  f1 : (tableEnvelope C).f1 13133 165 ≤ (702970111 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (337918287 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13133 165 ≤ (1657779191 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13133 165 ≤ (294869563 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 13133 165 ≤ (8619021 / 2000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (86189453 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (86189453 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1312563071 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (48838909 / 12500000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((719569 / 200000000) : ℝ) ≤ √(17 / (100 * 13133) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13133) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1037963469 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18114656159 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13133) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13133) ≤ (107683969 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13133) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13133 * (165 : ℝ) ^ 2 + 26 / (10 * 13133) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13133) : ℝ)) (tA 13133 * 165 ^ 2 + 26 / (10 * 13133)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((719569 / 200000000))) * ((86189453 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((719569 / 200000000)) ^ 3) * ((1312563071 / 1000000000000000000000000))) + ((48838909 / 12500000000000000000000)) * (3 / 2 * (39895 / 100000) / ((719569 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13133) : ℝ)) d.D d.V d.P (√(tA 13133) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((719569 / 200000000)) ^ 2 * (((1037963469 / 500000000000000)) * ((18114656159 / 500000000000000000)))) + ((48838909 / 12500000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13133) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((719569 / 200000000)) * ((86189453 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13133) : ℝ)) (tA 13133 * 165 ^ 2 + 26 / (10 * 13133)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((86189453 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((719569 / 200000000)) ^ 2) * ((1312563071 / 1000000000000000000000000)) + ((48838909 / 12500000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13133) : ℝ)) (√(26 / (10 * 13133) : ℝ)) d.D d.V d.P (√(tA 13133) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((719569 / 200000000)) * (((1037963469 / 500000000000000)) * ((18114656159 / 500000000000000000))) + ((48838909 / 12500000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13133) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((86189453 / 20000000000000000000) : ℝ) + ((48838909 / 12500000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13133

namespace BstLean.Part266.Row13133
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13133 165 ∧
    0 ≤ (tableEnvelope C).f1 13133 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13133 165 ∧
    0 ≤ (tableEnvelope C).w1 13133 165 ∧ 0 ≤ (tableEnvelope C).w2 13133 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13133 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13133 165 ∧ 0 ≤ d.f1 13133 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13133 165 ∧ 0 ≤ d.w1 13133 165 ∧ 0 ≤ d.w2 13133 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13133 ≤ 2 * (228 / 100 : ℝ) / 13133 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13133 ≤ 2 * (370 / 100 : ℝ) / 13133 := by
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
    (completeRAData (tableEnvelope C) 13133 165).locationBound 13133 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13133 165).energyBound 13133 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13133 165) (d.f1 13133 165) d.f2 ≤
      32 * (((842847049 / 200000000000000000) : ℝ) + (702970111 / 500000000000000000) + (337918287 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13133 165) (d.w1 13133 165)
      (d.w2 13133 165) ≤
      32 * (((1657779191 / 100000000000000000000) : ℝ) + (294869563 / 25000000000000000000) + (8619021 / 2000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13133 165) (d.f1 13133 165) d.f2 ≤
      ((842847049 / 200000000000000000) : ℝ) ^ 2 + 2 * ((842847049 / 200000000000000000)) * ((702970111 / 500000000000000000)) * (126 / 100) +
      2 * (((702970111 / 500000000000000000)) ^ 2 + 2 * ((842847049 / 200000000000000000)) * ((337918287 / 1000000000000000000))) +
      6 * ((702970111 / 500000000000000000)) * ((337918287 / 1000000000000000000)) * (126 / 100) + 8 * ((337918287 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13133 165) (d.f1 13133 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13133 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13133 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13133 165) (d.f1 13133 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13133 165) (d.w1 13133 165) (d.w2 13133 165)
  have hwexpr0 : 0 ≤ d.w0 13133 165 + d.w1 13133 165 * √(π / 2) +
      2 * d.w2 13133 165 + energyR16 13133 *
      radiusPolynomialRoot16 (d.w0 13133 165) (d.w1 13133 165) (d.w2 13133 165) := by
    positivity
  constructor
  · change (13133 : ℝ) ^ 8 * (mA 13133 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13133 165) (d.f1 13133 165) d.f2 + locationR16 13133 *
        radiusPolynomialRoot16 (d.f0 13133 165) (d.f1 13133 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13133 : ℝ) ^ 8 * (mA 13133 : ℝ) ^ 8 *
        ((((842847049 / 200000000000000000) : ℝ) ^ 2 + 2 * ((842847049 / 200000000000000000)) * ((702970111 / 500000000000000000)) * (126 / 100) +
          2 * (((702970111 / 500000000000000000)) ^ 2 + 2 * ((842847049 / 200000000000000000)) * ((337918287 / 1000000000000000000))) +
          6 * ((702970111 / 500000000000000000)) * ((337918287 / 1000000000000000000)) * (126 / 100) + 8 * ((337918287 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13133) *
          (32 * (((842847049 / 200000000000000000) : ℝ) + (702970111 / 500000000000000000) + (337918287 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13133 : ℝ) ^ 16 *
      (d.w0 13133 165 + d.w1 13133 165 * √(π / 2) + 2 * d.w2 13133 165 +
        energyR16 13133 * radiusPolynomialRoot16 (d.w0 13133 165) (d.w1 13133 165)
          (d.w2 13133 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13133 : ℝ) ^ 16 *
        (((1657779191 / 100000000000000000000) : ℝ) + ((294869563 / 25000000000000000000)) * (126 / 100) + 2 * ((8619021 / 2000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13133) *
          (32 * (((1657779191 / 100000000000000000000) : ℝ) + (294869563 / 25000000000000000000) + (8619021 / 2000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13133

/-! A coarse bound on the actual paper statistics constant at dimension 13134. -/
namespace BstLean.Part266.Row13134
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13132 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13132 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13132 128 ≤ (13386 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13386 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13134) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13134 : ℕ))
    (by norm_num : (13134 : ℕ) ≤ 16384)
  have ht : paperTail256 13134 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13134 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13134 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13134 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13134 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13134 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13132 128 * √(2 / (13134 : ℝ)) *
      (√(13134 : ℝ) + paperT0 13134 + paperTail256 13134) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13134 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13134 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13134 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13132 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13132 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13134 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13134

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13134
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13134 (61 / 100) 165 (17 / (100 * 13134)) (26 / (10 * 13134)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13134 (61 / 100) 165 (17 / (100 * 13134)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (6732013 / 1562500000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (328040839 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (976177827 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13134 / 13134 * (61 / 100)) ^ 4 * inverseRadius8 (13134 - 1) /
            envelopeGap 13134 (61 / 100) 165 (17 / (100 * 13134)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13134

namespace BstLean.Part266.Row13134
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13134 165 ≤ (4213433183 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13134 165 ≤ (1405672629 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (21115873 / 62500000000000000)
  w0 : (tableEnvelope C).w0 13134 165 ≤ (1657400559 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13134 165 ≤ (1179208857 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13134 165 ≤ (86170523 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (6732013 / 1562500000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (6732013 / 1562500000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (328040839 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (976177827 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((899427 / 250000000) : ℝ) ≤ √(17 / (100 * 13134) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13134) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1037844921 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36223795439 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13134) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13134) ≤ (10767577 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13134) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13134 * (165 : ℝ) ^ 2 + 26 / (10 * 13134) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13134) : ℝ)) (tA 13134 * 165 ^ 2 + 26 / (10 * 13134)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((899427 / 250000000))) * ((6732013 / 1562500000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((899427 / 250000000)) ^ 3) * ((328040839 / 250000000000000000000000))) + ((976177827 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((899427 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13134) : ℝ)) d.D d.V d.P (√(tA 13134) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((899427 / 250000000)) ^ 2 * (((1037844921 / 500000000000000)) * ((36223795439 / 1000000000000000000)))) + ((976177827 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13134) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((899427 / 250000000)) * ((6732013 / 1562500000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13134) : ℝ)) (tA 13134 * 165 ^ 2 + 26 / (10 * 13134)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((6732013 / 1562500000000000000) : ℝ) + (24198 / 100000) / (2 * ((899427 / 250000000)) ^ 2) * ((328040839 / 250000000000000000000000)) + ((976177827 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13134) : ℝ)) (√(26 / (10 * 13134) : ℝ)) d.D d.V d.P (√(tA 13134) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((899427 / 250000000)) * (((1037844921 / 500000000000000)) * ((36223795439 / 1000000000000000000))) + ((976177827 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13134) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((6732013 / 1562500000000000000) : ℝ) + ((976177827 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13134

namespace BstLean.Part266.Row13134
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13134 165 ∧
    0 ≤ (tableEnvelope C).f1 13134 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13134 165 ∧
    0 ≤ (tableEnvelope C).w1 13134 165 ∧ 0 ≤ (tableEnvelope C).w2 13134 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13134 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13134 165 ∧ 0 ≤ d.f1 13134 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13134 165 ∧ 0 ≤ d.w1 13134 165 ∧ 0 ≤ d.w2 13134 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13134 ≤ 2 * (228 / 100 : ℝ) / 13134 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13134 ≤ 2 * (370 / 100 : ℝ) / 13134 := by
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
    (completeRAData (tableEnvelope C) 13134 165).locationBound 13134 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13134 165).energyBound 13134 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13134 165) (d.f1 13134 165) d.f2 ≤
      32 * (((4213433183 / 1000000000000000000) : ℝ) + (1405672629 / 1000000000000000000) + (21115873 / 62500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13134 165) (d.w1 13134 165)
      (d.w2 13134 165) ≤
      32 * (((1657400559 / 100000000000000000000) : ℝ) + (1179208857 / 100000000000000000000) + (86170523 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13134 165) (d.f1 13134 165) d.f2 ≤
      ((4213433183 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4213433183 / 1000000000000000000)) * ((1405672629 / 1000000000000000000)) * (126 / 100) +
      2 * (((1405672629 / 1000000000000000000)) ^ 2 + 2 * ((4213433183 / 1000000000000000000)) * ((21115873 / 62500000000000000))) +
      6 * ((1405672629 / 1000000000000000000)) * ((21115873 / 62500000000000000)) * (126 / 100) + 8 * ((21115873 / 62500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13134 165) (d.f1 13134 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13134 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13134 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13134 165) (d.f1 13134 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13134 165) (d.w1 13134 165) (d.w2 13134 165)
  have hwexpr0 : 0 ≤ d.w0 13134 165 + d.w1 13134 165 * √(π / 2) +
      2 * d.w2 13134 165 + energyR16 13134 *
      radiusPolynomialRoot16 (d.w0 13134 165) (d.w1 13134 165) (d.w2 13134 165) := by
    positivity
  constructor
  · change (13134 : ℝ) ^ 8 * (mA 13134 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13134 165) (d.f1 13134 165) d.f2 + locationR16 13134 *
        radiusPolynomialRoot16 (d.f0 13134 165) (d.f1 13134 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13134 : ℝ) ^ 8 * (mA 13134 : ℝ) ^ 8 *
        ((((4213433183 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4213433183 / 1000000000000000000)) * ((1405672629 / 1000000000000000000)) * (126 / 100) +
          2 * (((1405672629 / 1000000000000000000)) ^ 2 + 2 * ((4213433183 / 1000000000000000000)) * ((21115873 / 62500000000000000))) +
          6 * ((1405672629 / 1000000000000000000)) * ((21115873 / 62500000000000000)) * (126 / 100) + 8 * ((21115873 / 62500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13134) *
          (32 * (((4213433183 / 1000000000000000000) : ℝ) + (1405672629 / 1000000000000000000) + (21115873 / 62500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13134 : ℝ) ^ 16 *
      (d.w0 13134 165 + d.w1 13134 165 * √(π / 2) + 2 * d.w2 13134 165 +
        energyR16 13134 * radiusPolynomialRoot16 (d.w0 13134 165) (d.w1 13134 165)
          (d.w2 13134 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13134 : ℝ) ^ 16 *
        (((1657400559 / 100000000000000000000) : ℝ) + ((1179208857 / 100000000000000000000)) * (126 / 100) + 2 * ((86170523 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13134) *
          (32 * (((1657400559 / 100000000000000000000) : ℝ) + (1179208857 / 100000000000000000000) + (86170523 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13134

/-! A coarse bound on the actual paper statistics constant at dimension 13135. -/
namespace BstLean.Part266.Row13135
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13133 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13133 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13133 128 ≤ (13387 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13387 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13135) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13135 : ℕ))
    (by norm_num : (13135 : ℕ) ≤ 16384)
  have ht : paperTail256 13135 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13135 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13135 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13135 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13135 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13135 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13133 128 * √(2 / (13135 : ℝ)) *
      (√(13135 : ℝ) + paperT0 13135 + paperTail256 13135) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13135 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13135 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13135 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13133 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13133 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13135 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13135

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13135
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13135 (61 / 100) 165 (17 / (100 * 13135)) (26 / (10 * 13135)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13135 (61 / 100) 165 (17 / (100 * 13135)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (43075043 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (655881897 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3902311559 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13135 / 13135 * (61 / 100)) ^ 4 * inverseRadius8 (13135 - 1) /
            envelopeGap 13135 (61 / 100) 165 (17 / (100 * 13135)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13135

namespace BstLean.Part266.Row13135
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13135 165 ≤ (421263139 / 100000000000000000)
  f1 : (tableEnvelope C).f1 13135 165 ≤ (1405405121 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (84447417 / 250000000000000000)
  w0 : (tableEnvelope C).w0 13135 165 ≤ (828511027 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13135 165 ≤ (1178939551 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13135 165 ≤ (430754211 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (43075043 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (43075043 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (655881897 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3902311559 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3597571 / 1000000000) : ℝ) ≤ √(17 / (100 * 13135) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13135) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1037726397 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36218279833 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13135) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13135) ≤ (107667573 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13135) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13135 * (165 : ℝ) ^ 2 + 26 / (10 * 13135) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13135) : ℝ)) (tA 13135 * 165 ^ 2 + 26 / (10 * 13135)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3597571 / 1000000000))) * ((43075043 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3597571 / 1000000000)) ^ 3) * ((655881897 / 500000000000000000000000))) + ((3902311559 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3597571 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13135) : ℝ)) d.D d.V d.P (√(tA 13135) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3597571 / 1000000000)) ^ 2 * (((1037726397 / 500000000000000)) * ((36218279833 / 1000000000000000000)))) + ((3902311559 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13135) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3597571 / 1000000000)) * ((43075043 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13135) : ℝ)) (tA 13135 * 165 ^ 2 + 26 / (10 * 13135)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((43075043 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3597571 / 1000000000)) ^ 2) * ((655881897 / 500000000000000000000000)) + ((3902311559 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13135) : ℝ)) (√(26 / (10 * 13135) : ℝ)) d.D d.V d.P (√(tA 13135) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3597571 / 1000000000)) * (((1037726397 / 500000000000000)) * ((36218279833 / 1000000000000000000))) + ((3902311559 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13135) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((43075043 / 10000000000000000000) : ℝ) + ((3902311559 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13135

namespace BstLean.Part266.Row13135
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13135 165 ∧
    0 ≤ (tableEnvelope C).f1 13135 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13135 165 ∧
    0 ≤ (tableEnvelope C).w1 13135 165 ∧ 0 ≤ (tableEnvelope C).w2 13135 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13135 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13135 165 ∧ 0 ≤ d.f1 13135 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13135 165 ∧ 0 ≤ d.w1 13135 165 ∧ 0 ≤ d.w2 13135 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13135 ≤ 2 * (228 / 100 : ℝ) / 13135 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13135 ≤ 2 * (370 / 100 : ℝ) / 13135 := by
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
    (completeRAData (tableEnvelope C) 13135 165).locationBound 13135 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13135 165).energyBound 13135 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13135 165) (d.f1 13135 165) d.f2 ≤
      32 * (((421263139 / 100000000000000000) : ℝ) + (1405405121 / 1000000000000000000) + (84447417 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13135 165) (d.w1 13135 165)
      (d.w2 13135 165) ≤
      32 * (((828511027 / 50000000000000000000) : ℝ) + (1178939551 / 100000000000000000000) + (430754211 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13135 165) (d.f1 13135 165) d.f2 ≤
      ((421263139 / 100000000000000000) : ℝ) ^ 2 + 2 * ((421263139 / 100000000000000000)) * ((1405405121 / 1000000000000000000)) * (126 / 100) +
      2 * (((1405405121 / 1000000000000000000)) ^ 2 + 2 * ((421263139 / 100000000000000000)) * ((84447417 / 250000000000000000))) +
      6 * ((1405405121 / 1000000000000000000)) * ((84447417 / 250000000000000000)) * (126 / 100) + 8 * ((84447417 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13135 165) (d.f1 13135 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13135 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13135 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13135 165) (d.f1 13135 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13135 165) (d.w1 13135 165) (d.w2 13135 165)
  have hwexpr0 : 0 ≤ d.w0 13135 165 + d.w1 13135 165 * √(π / 2) +
      2 * d.w2 13135 165 + energyR16 13135 *
      radiusPolynomialRoot16 (d.w0 13135 165) (d.w1 13135 165) (d.w2 13135 165) := by
    positivity
  constructor
  · change (13135 : ℝ) ^ 8 * (mA 13135 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13135 165) (d.f1 13135 165) d.f2 + locationR16 13135 *
        radiusPolynomialRoot16 (d.f0 13135 165) (d.f1 13135 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13135 : ℝ) ^ 8 * (mA 13135 : ℝ) ^ 8 *
        ((((421263139 / 100000000000000000) : ℝ) ^ 2 + 2 * ((421263139 / 100000000000000000)) * ((1405405121 / 1000000000000000000)) * (126 / 100) +
          2 * (((1405405121 / 1000000000000000000)) ^ 2 + 2 * ((421263139 / 100000000000000000)) * ((84447417 / 250000000000000000))) +
          6 * ((1405405121 / 1000000000000000000)) * ((84447417 / 250000000000000000)) * (126 / 100) + 8 * ((84447417 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13135) *
          (32 * (((421263139 / 100000000000000000) : ℝ) + (1405405121 / 1000000000000000000) + (84447417 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13135 : ℝ) ^ 16 *
      (d.w0 13135 165 + d.w1 13135 165 * √(π / 2) + 2 * d.w2 13135 165 +
        energyR16 13135 * radiusPolynomialRoot16 (d.w0 13135 165) (d.w1 13135 165)
          (d.w2 13135 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13135 : ℝ) ^ 16 *
        (((828511027 / 50000000000000000000) : ℝ) + ((1178939551 / 100000000000000000000)) * (126 / 100) + 2 * ((430754211 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13135) *
          (32 * (((828511027 / 50000000000000000000) : ℝ) + (1178939551 / 100000000000000000000) + (430754211 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13135

/-! A coarse bound on the actual paper statistics constant at dimension 13136. -/
namespace BstLean.Part266.Row13136
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13134 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13134 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13134 128 ≤ (13388 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13388 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13136) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13136 : ℕ))
    (by norm_num : (13136 : ℕ) ≤ 16384)
  have ht : paperTail256 13136 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13136 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13136 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13136 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13136 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13136 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13134 128 * √(2 / (13136 : ℝ)) *
      (√(13136 : ℝ) + paperT0 13136 + paperTail256 13136) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13136 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13136 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13136 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13134 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13134 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13136 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13136

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13136
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13136 (61 / 100) 165 (17 / (100 * 13136)) (26 / (10 * 13136)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13136 (61 / 100) 165 (17 / (100 * 13136)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (215326029 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1311364383 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3899913469 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13136 / 13136 * (61 / 100)) ^ 4 * inverseRadius8 (13136 - 1) /
            envelopeGap 13136 (61 / 100) 165 (17 / (100 * 13136)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13136

namespace BstLean.Part266.Row13136
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13136 165 ≤ (210591493 / 50000000000000000)
  f1 : (tableEnvelope C).f1 13136 165 ≤ (1405137697 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (337725387 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13136 165 ≤ (828321837 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13136 165 ≤ (1178670333 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13136 165 ≤ (107663959 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (215326029 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (215326029 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1311364383 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3899913469 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1798717 / 500000000) : ℝ) ≤ √(17 / (100 * 13136) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13136) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (129700987 / 62500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36212765471 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13136) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13136) ≤ (6728711 / 62500000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13136) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13136 * (165 : ℝ) ^ 2 + 26 / (10 * 13136) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13136) : ℝ)) (tA 13136 * 165 ^ 2 + 26 / (10 * 13136)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1798717 / 500000000))) * ((215326029 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1798717 / 500000000)) ^ 3) * ((1311364383 / 1000000000000000000000000))) + ((3899913469 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1798717 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13136) : ℝ)) d.D d.V d.P (√(tA 13136) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1798717 / 500000000)) ^ 2 * (((129700987 / 62500000000000)) * ((36212765471 / 1000000000000000000)))) + ((3899913469 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13136) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1798717 / 500000000)) * ((215326029 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13136) : ℝ)) (tA 13136 * 165 ^ 2 + 26 / (10 * 13136)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((215326029 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1798717 / 500000000)) ^ 2) * ((1311364383 / 1000000000000000000000000)) + ((3899913469 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13136) : ℝ)) (√(26 / (10 * 13136) : ℝ)) d.D d.V d.P (√(tA 13136) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1798717 / 500000000)) * (((129700987 / 62500000000000)) * ((36212765471 / 1000000000000000000))) + ((3899913469 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13136) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((215326029 / 50000000000000000000) : ℝ) + ((3899913469 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13136

namespace BstLean.Part266.Row13136
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13136 165 ∧
    0 ≤ (tableEnvelope C).f1 13136 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13136 165 ∧
    0 ≤ (tableEnvelope C).w1 13136 165 ∧ 0 ≤ (tableEnvelope C).w2 13136 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13136 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13136 165 ∧ 0 ≤ d.f1 13136 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13136 165 ∧ 0 ≤ d.w1 13136 165 ∧ 0 ≤ d.w2 13136 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13136 ≤ 2 * (228 / 100 : ℝ) / 13136 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13136 ≤ 2 * (370 / 100 : ℝ) / 13136 := by
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
    (completeRAData (tableEnvelope C) 13136 165).locationBound 13136 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13136 165).energyBound 13136 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13136 165) (d.f1 13136 165) d.f2 ≤
      32 * (((210591493 / 50000000000000000) : ℝ) + (1405137697 / 1000000000000000000) + (337725387 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13136 165) (d.w1 13136 165)
      (d.w2 13136 165) ≤
      32 * (((828321837 / 50000000000000000000) : ℝ) + (1178670333 / 100000000000000000000) + (107663959 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13136 165) (d.f1 13136 165) d.f2 ≤
      ((210591493 / 50000000000000000) : ℝ) ^ 2 + 2 * ((210591493 / 50000000000000000)) * ((1405137697 / 1000000000000000000)) * (126 / 100) +
      2 * (((1405137697 / 1000000000000000000)) ^ 2 + 2 * ((210591493 / 50000000000000000)) * ((337725387 / 1000000000000000000))) +
      6 * ((1405137697 / 1000000000000000000)) * ((337725387 / 1000000000000000000)) * (126 / 100) + 8 * ((337725387 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13136 165) (d.f1 13136 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13136 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13136 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13136 165) (d.f1 13136 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13136 165) (d.w1 13136 165) (d.w2 13136 165)
  have hwexpr0 : 0 ≤ d.w0 13136 165 + d.w1 13136 165 * √(π / 2) +
      2 * d.w2 13136 165 + energyR16 13136 *
      radiusPolynomialRoot16 (d.w0 13136 165) (d.w1 13136 165) (d.w2 13136 165) := by
    positivity
  constructor
  · change (13136 : ℝ) ^ 8 * (mA 13136 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13136 165) (d.f1 13136 165) d.f2 + locationR16 13136 *
        radiusPolynomialRoot16 (d.f0 13136 165) (d.f1 13136 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13136 : ℝ) ^ 8 * (mA 13136 : ℝ) ^ 8 *
        ((((210591493 / 50000000000000000) : ℝ) ^ 2 + 2 * ((210591493 / 50000000000000000)) * ((1405137697 / 1000000000000000000)) * (126 / 100) +
          2 * (((1405137697 / 1000000000000000000)) ^ 2 + 2 * ((210591493 / 50000000000000000)) * ((337725387 / 1000000000000000000))) +
          6 * ((1405137697 / 1000000000000000000)) * ((337725387 / 1000000000000000000)) * (126 / 100) + 8 * ((337725387 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13136) *
          (32 * (((210591493 / 50000000000000000) : ℝ) + (1405137697 / 1000000000000000000) + (337725387 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13136 : ℝ) ^ 16 *
      (d.w0 13136 165 + d.w1 13136 165 * √(π / 2) + 2 * d.w2 13136 165 +
        energyR16 13136 * radiusPolynomialRoot16 (d.w0 13136 165) (d.w1 13136 165)
          (d.w2 13136 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13136 : ℝ) ^ 16 *
        (((828321837 / 50000000000000000000) : ℝ) + ((1178670333 / 100000000000000000000)) * (126 / 100) + 2 * ((107663959 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13136) *
          (32 * (((828321837 / 50000000000000000000) : ℝ) + (1178670333 / 100000000000000000000) + (107663959 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13136

/-! A coarse bound on the actual paper statistics constant at dimension 13137. -/
namespace BstLean.Part266.Row13137
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13135 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13135 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13135 128 ≤ (13389 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13389 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13137) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13137 : ℕ))
    (by norm_num : (13137 : ℕ) ≤ 16384)
  have ht : paperTail256 13137 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13137 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13137 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13137 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13137 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13137 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13135 128 * √(2 / (13137 : ℝ)) *
      (√(13137 : ℝ) + paperT0 13137 + paperTail256 13137) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13137 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13137 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13137 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13135 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13135 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13137 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13137

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13137
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13137 (61 / 100) 165 (17 / (100 * 13137)) (26 / (10 * 13137)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13137 (61 / 100) 165 (17 / (100 * 13137)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (86110743 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (10487721 / 8000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (48718963 / 12500000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13137 / 13137 * (61 / 100)) ^ 4 * inverseRadius8 (13137 - 1) /
            envelopeGap 13137 (61 / 100) 165 (17 / (100 * 13137)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13137

namespace BstLean.Part266.Row13137
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13137 165 ≤ (4211028599 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13137 165 ≤ (280974071 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (337661123 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13137 165 ≤ (1656265421 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13137 165 ≤ (2946003 / 250000000000000000)
  w2 : (tableEnvelope C).w2 13137 165 ≤ (430557491 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (86110743 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (86110743 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (10487721 / 8000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (48718963 / 12500000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3597297 / 1000000000) : ℝ) ≤ √(17 / (100 * 13137) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13137) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (129686177 / 62500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18103626191 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13137) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13137) ≤ (107651181 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13137) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13137 * (165 : ℝ) ^ 2 + 26 / (10 * 13137) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13137) : ℝ)) (tA 13137 * 165 ^ 2 + 26 / (10 * 13137)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3597297 / 1000000000))) * ((86110743 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3597297 / 1000000000)) ^ 3) * ((10487721 / 8000000000000000000000))) + ((48718963 / 12500000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3597297 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13137) : ℝ)) d.D d.V d.P (√(tA 13137) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3597297 / 1000000000)) ^ 2 * (((129686177 / 62500000000000)) * ((18103626191 / 500000000000000000)))) + ((48718963 / 12500000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13137) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3597297 / 1000000000)) * ((86110743 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13137) : ℝ)) (tA 13137 * 165 ^ 2 + 26 / (10 * 13137)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((86110743 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3597297 / 1000000000)) ^ 2) * ((10487721 / 8000000000000000000000)) + ((48718963 / 12500000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13137) : ℝ)) (√(26 / (10 * 13137) : ℝ)) d.D d.V d.P (√(tA 13137) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3597297 / 1000000000)) * (((129686177 / 62500000000000)) * ((18103626191 / 500000000000000000))) + ((48718963 / 12500000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13137) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((86110743 / 20000000000000000000) : ℝ) + ((48718963 / 12500000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13137

namespace BstLean.Part266.Row13137
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13137 165 ∧
    0 ≤ (tableEnvelope C).f1 13137 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13137 165 ∧
    0 ≤ (tableEnvelope C).w1 13137 165 ∧ 0 ≤ (tableEnvelope C).w2 13137 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13137 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13137 165 ∧ 0 ≤ d.f1 13137 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13137 165 ∧ 0 ≤ d.w1 13137 165 ∧ 0 ≤ d.w2 13137 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13137 ≤ 2 * (228 / 100 : ℝ) / 13137 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13137 ≤ 2 * (370 / 100 : ℝ) / 13137 := by
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
    (completeRAData (tableEnvelope C) 13137 165).locationBound 13137 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13137 165).energyBound 13137 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13137 165) (d.f1 13137 165) d.f2 ≤
      32 * (((4211028599 / 1000000000000000000) : ℝ) + (280974071 / 200000000000000000) + (337661123 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13137 165) (d.w1 13137 165)
      (d.w2 13137 165) ≤
      32 * (((1656265421 / 100000000000000000000) : ℝ) + (2946003 / 250000000000000000) + (430557491 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13137 165) (d.f1 13137 165) d.f2 ≤
      ((4211028599 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4211028599 / 1000000000000000000)) * ((280974071 / 200000000000000000)) * (126 / 100) +
      2 * (((280974071 / 200000000000000000)) ^ 2 + 2 * ((4211028599 / 1000000000000000000)) * ((337661123 / 1000000000000000000))) +
      6 * ((280974071 / 200000000000000000)) * ((337661123 / 1000000000000000000)) * (126 / 100) + 8 * ((337661123 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13137 165) (d.f1 13137 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13137 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13137 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13137 165) (d.f1 13137 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13137 165) (d.w1 13137 165) (d.w2 13137 165)
  have hwexpr0 : 0 ≤ d.w0 13137 165 + d.w1 13137 165 * √(π / 2) +
      2 * d.w2 13137 165 + energyR16 13137 *
      radiusPolynomialRoot16 (d.w0 13137 165) (d.w1 13137 165) (d.w2 13137 165) := by
    positivity
  constructor
  · change (13137 : ℝ) ^ 8 * (mA 13137 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13137 165) (d.f1 13137 165) d.f2 + locationR16 13137 *
        radiusPolynomialRoot16 (d.f0 13137 165) (d.f1 13137 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13137 : ℝ) ^ 8 * (mA 13137 : ℝ) ^ 8 *
        ((((4211028599 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4211028599 / 1000000000000000000)) * ((280974071 / 200000000000000000)) * (126 / 100) +
          2 * (((280974071 / 200000000000000000)) ^ 2 + 2 * ((4211028599 / 1000000000000000000)) * ((337661123 / 1000000000000000000))) +
          6 * ((280974071 / 200000000000000000)) * ((337661123 / 1000000000000000000)) * (126 / 100) + 8 * ((337661123 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13137) *
          (32 * (((4211028599 / 1000000000000000000) : ℝ) + (280974071 / 200000000000000000) + (337661123 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13137 : ℝ) ^ 16 *
      (d.w0 13137 165 + d.w1 13137 165 * √(π / 2) + 2 * d.w2 13137 165 +
        energyR16 13137 * radiusPolynomialRoot16 (d.w0 13137 165) (d.w1 13137 165)
          (d.w2 13137 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13137 : ℝ) ^ 16 *
        (((1656265421 / 100000000000000000000) : ℝ) + ((2946003 / 250000000000000000)) * (126 / 100) + 2 * ((430557491 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13137) *
          (32 * (((1656265421 / 100000000000000000000) : ℝ) + (2946003 / 250000000000000000) + (430557491 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13137

/-! A coarse bound on the actual paper statistics constant at dimension 13138. -/
namespace BstLean.Part266.Row13138
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13136 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13136 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13136 128 ≤ (13390 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13390 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13138) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13138 : ℕ))
    (by norm_num : (13138 : ℕ) ≤ 16384)
  have ht : paperTail256 13138 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13138 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13138 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13138 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13138 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13138 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13136 128 * √(2 / (13138 : ℝ)) *
      (√(13138 : ℝ) + paperT0 13138 + paperTail256 13138) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13138 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13138 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13138 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13136 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13136 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13138 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13138

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13138
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13138 (61 / 100) 165 (17 / (100 * 13138)) (26 / (10 * 13138)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13138 (61 / 100) 165 (17 / (100 * 13138)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (430455403 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (655283009 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (973780567 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13138 / 13138 * (61 / 100)) ^ 4 * inverseRadius8 (13138 - 1) /
            envelopeGap 13138 (61 / 100) 165 (17 / (100 * 13138)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13138

namespace BstLean.Part266.Row13138
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13138 165 ≤ (2105113801 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13138 165 ≤ (175575387 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (4219961 / 12500000000000000)
  w0 : (tableEnvelope C).w0 13138 165 ≤ (1655887293 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13138 165 ≤ (589066077 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13138 165 ≤ (430459177 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (430455403 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (430455403 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (655283009 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (973780567 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((89929 / 25000000) : ℝ) ≤ √(17 / (100 * 13138) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13138) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2074741919 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36201740539 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13138) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13138) ≤ (107642987 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13138) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13138 * (165 : ℝ) ^ 2 + 26 / (10 * 13138) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13138) : ℝ)) (tA 13138 * 165 ^ 2 + 26 / (10 * 13138)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((89929 / 25000000))) * ((430455403 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((89929 / 25000000)) ^ 3) * ((655283009 / 500000000000000000000000))) + ((973780567 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((89929 / 25000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13138) : ℝ)) d.D d.V d.P (√(tA 13138) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((89929 / 25000000)) ^ 2 * (((2074741919 / 1000000000000000)) * ((36201740539 / 1000000000000000000)))) + ((973780567 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13138) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((89929 / 25000000)) * ((430455403 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13138) : ℝ)) (tA 13138 * 165 ^ 2 + 26 / (10 * 13138)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((430455403 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((89929 / 25000000)) ^ 2) * ((655283009 / 500000000000000000000000)) + ((973780567 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13138) : ℝ)) (√(26 / (10 * 13138) : ℝ)) d.D d.V d.P (√(tA 13138) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((89929 / 25000000)) * (((2074741919 / 1000000000000000)) * ((36201740539 / 1000000000000000000))) + ((973780567 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13138) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((430455403 / 100000000000000000000) : ℝ) + ((973780567 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13138

namespace BstLean.Part266.Row13138
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13138 165 ∧
    0 ≤ (tableEnvelope C).f1 13138 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13138 165 ∧
    0 ≤ (tableEnvelope C).w1 13138 165 ∧ 0 ≤ (tableEnvelope C).w2 13138 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13138 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13138 165 ∧ 0 ≤ d.f1 13138 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13138 165 ∧ 0 ≤ d.w1 13138 165 ∧ 0 ≤ d.w2 13138 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13138 ≤ 2 * (228 / 100 : ℝ) / 13138 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13138 ≤ 2 * (370 / 100 : ℝ) / 13138 := by
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
    (completeRAData (tableEnvelope C) 13138 165).locationBound 13138 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13138 165).energyBound 13138 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13138 165) (d.f1 13138 165) d.f2 ≤
      32 * (((2105113801 / 500000000000000000) : ℝ) + (175575387 / 125000000000000000) + (4219961 / 12500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13138 165) (d.w1 13138 165)
      (d.w2 13138 165) ≤
      32 * (((1655887293 / 100000000000000000000) : ℝ) + (589066077 / 50000000000000000000) + (430459177 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13138 165) (d.f1 13138 165) d.f2 ≤
      ((2105113801 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2105113801 / 500000000000000000)) * ((175575387 / 125000000000000000)) * (126 / 100) +
      2 * (((175575387 / 125000000000000000)) ^ 2 + 2 * ((2105113801 / 500000000000000000)) * ((4219961 / 12500000000000000))) +
      6 * ((175575387 / 125000000000000000)) * ((4219961 / 12500000000000000)) * (126 / 100) + 8 * ((4219961 / 12500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13138 165) (d.f1 13138 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13138 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13138 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13138 165) (d.f1 13138 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13138 165) (d.w1 13138 165) (d.w2 13138 165)
  have hwexpr0 : 0 ≤ d.w0 13138 165 + d.w1 13138 165 * √(π / 2) +
      2 * d.w2 13138 165 + energyR16 13138 *
      radiusPolynomialRoot16 (d.w0 13138 165) (d.w1 13138 165) (d.w2 13138 165) := by
    positivity
  constructor
  · change (13138 : ℝ) ^ 8 * (mA 13138 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13138 165) (d.f1 13138 165) d.f2 + locationR16 13138 *
        radiusPolynomialRoot16 (d.f0 13138 165) (d.f1 13138 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13138 : ℝ) ^ 8 * (mA 13138 : ℝ) ^ 8 *
        ((((2105113801 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2105113801 / 500000000000000000)) * ((175575387 / 125000000000000000)) * (126 / 100) +
          2 * (((175575387 / 125000000000000000)) ^ 2 + 2 * ((2105113801 / 500000000000000000)) * ((4219961 / 12500000000000000))) +
          6 * ((175575387 / 125000000000000000)) * ((4219961 / 12500000000000000)) * (126 / 100) + 8 * ((4219961 / 12500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13138) *
          (32 * (((2105113801 / 500000000000000000) : ℝ) + (175575387 / 125000000000000000) + (4219961 / 12500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13138 : ℝ) ^ 16 *
      (d.w0 13138 165 + d.w1 13138 165 * √(π / 2) + 2 * d.w2 13138 165 +
        energyR16 13138 * radiusPolynomialRoot16 (d.w0 13138 165) (d.w1 13138 165)
          (d.w2 13138 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13138 : ℝ) ^ 16 *
        (((1655887293 / 100000000000000000000) : ℝ) + ((589066077 / 50000000000000000000)) * (126 / 100) + 2 * ((430459177 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13138) *
          (32 * (((1655887293 / 100000000000000000000) : ℝ) + (589066077 / 50000000000000000000) + (430459177 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13138

/-! A coarse bound on the actual paper statistics constant at dimension 13139. -/
namespace BstLean.Part266.Row13139
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13137 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13137 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13137 128 ≤ (13391 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13391 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13139) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13139 : ℕ))
    (by norm_num : (13139 : ℕ) ≤ 16384)
  have ht : paperTail256 13139 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13139 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13139 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13139 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13139 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13139 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13137 128 * √(2 / (13139 : ℝ)) *
      (√(13139 : ℝ) + paperT0 13139 + paperTail256 13139) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13139 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13139 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13139 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13137 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13137 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13139 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13139

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13139
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13139 (61 / 100) 165 (17 / (100 * 13139)) (26 / (10 * 13139)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13139 (61 / 100) 165 (17 / (100 * 13139)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (672433 / 156250000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (163770883 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3892729153 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13139 / 13139 * (61 / 100)) ^ 4 * inverseRadius8 (13139 - 1) /
            envelopeGap 13139 (61 / 100) 165 (17 / (100 * 13139)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13139

namespace BstLean.Part266.Row13139
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13139 165 ≤ (2104713437 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13139 165 ≤ (702167961 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (337532653 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13139 165 ≤ (1655509291 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13139 165 ≤ (294465799 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 13139 165 ≤ (430360891 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (672433 / 156250000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (672433 / 156250000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (163770883 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3892729153 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3597023 / 1000000000) : ℝ) ≤ √(17 / (100 * 13139) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13139) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (41490101 / 20000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3619622997 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13139) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13139) ≤ (21526959 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13139) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13139 * (165 : ℝ) ^ 2 + 26 / (10 * 13139) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13139) : ℝ)) (tA 13139 * 165 ^ 2 + 26 / (10 * 13139)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3597023 / 1000000000))) * ((672433 / 156250000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3597023 / 1000000000)) ^ 3) * ((163770883 / 125000000000000000000000))) + ((3892729153 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3597023 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13139) : ℝ)) d.D d.V d.P (√(tA 13139) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3597023 / 1000000000)) ^ 2 * (((41490101 / 20000000000000)) * ((3619622997 / 100000000000000000)))) + ((3892729153 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13139) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3597023 / 1000000000)) * ((672433 / 156250000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13139) : ℝ)) (tA 13139 * 165 ^ 2 + 26 / (10 * 13139)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((672433 / 156250000000000000) : ℝ) + (24198 / 100000) / (2 * ((3597023 / 1000000000)) ^ 2) * ((163770883 / 125000000000000000000000)) + ((3892729153 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13139) : ℝ)) (√(26 / (10 * 13139) : ℝ)) d.D d.V d.P (√(tA 13139) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3597023 / 1000000000)) * (((41490101 / 20000000000000)) * ((3619622997 / 100000000000000000))) + ((3892729153 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13139) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((672433 / 156250000000000000) : ℝ) + ((3892729153 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13139

namespace BstLean.Part266.Row13139
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13139 165 ∧
    0 ≤ (tableEnvelope C).f1 13139 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13139 165 ∧
    0 ≤ (tableEnvelope C).w1 13139 165 ∧ 0 ≤ (tableEnvelope C).w2 13139 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13139 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13139 165 ∧ 0 ≤ d.f1 13139 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13139 165 ∧ 0 ≤ d.w1 13139 165 ∧ 0 ≤ d.w2 13139 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13139 ≤ 2 * (228 / 100 : ℝ) / 13139 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13139 ≤ 2 * (370 / 100 : ℝ) / 13139 := by
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
    (completeRAData (tableEnvelope C) 13139 165).locationBound 13139 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13139 165).energyBound 13139 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13139 165) (d.f1 13139 165) d.f2 ≤
      32 * (((2104713437 / 500000000000000000) : ℝ) + (702167961 / 500000000000000000) + (337532653 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13139 165) (d.w1 13139 165)
      (d.w2 13139 165) ≤
      32 * (((1655509291 / 100000000000000000000) : ℝ) + (294465799 / 25000000000000000000) + (430360891 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13139 165) (d.f1 13139 165) d.f2 ≤
      ((2104713437 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2104713437 / 500000000000000000)) * ((702167961 / 500000000000000000)) * (126 / 100) +
      2 * (((702167961 / 500000000000000000)) ^ 2 + 2 * ((2104713437 / 500000000000000000)) * ((337532653 / 1000000000000000000))) +
      6 * ((702167961 / 500000000000000000)) * ((337532653 / 1000000000000000000)) * (126 / 100) + 8 * ((337532653 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13139 165) (d.f1 13139 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13139 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13139 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13139 165) (d.f1 13139 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13139 165) (d.w1 13139 165) (d.w2 13139 165)
  have hwexpr0 : 0 ≤ d.w0 13139 165 + d.w1 13139 165 * √(π / 2) +
      2 * d.w2 13139 165 + energyR16 13139 *
      radiusPolynomialRoot16 (d.w0 13139 165) (d.w1 13139 165) (d.w2 13139 165) := by
    positivity
  constructor
  · change (13139 : ℝ) ^ 8 * (mA 13139 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13139 165) (d.f1 13139 165) d.f2 + locationR16 13139 *
        radiusPolynomialRoot16 (d.f0 13139 165) (d.f1 13139 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13139 : ℝ) ^ 8 * (mA 13139 : ℝ) ^ 8 *
        ((((2104713437 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2104713437 / 500000000000000000)) * ((702167961 / 500000000000000000)) * (126 / 100) +
          2 * (((702167961 / 500000000000000000)) ^ 2 + 2 * ((2104713437 / 500000000000000000)) * ((337532653 / 1000000000000000000))) +
          6 * ((702167961 / 500000000000000000)) * ((337532653 / 1000000000000000000)) * (126 / 100) + 8 * ((337532653 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13139) *
          (32 * (((2104713437 / 500000000000000000) : ℝ) + (702167961 / 500000000000000000) + (337532653 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13139 : ℝ) ^ 16 *
      (d.w0 13139 165 + d.w1 13139 165 * √(π / 2) + 2 * d.w2 13139 165 +
        energyR16 13139 * radiusPolynomialRoot16 (d.w0 13139 165) (d.w1 13139 165)
          (d.w2 13139 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13139 : ℝ) ^ 16 *
        (((1655509291 / 100000000000000000000) : ℝ) + ((294465799 / 25000000000000000000)) * (126 / 100) + 2 * ((430360891 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13139) *
          (32 * (((1655509291 / 100000000000000000000) : ℝ) + (294465799 / 25000000000000000000) + (430360891 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13139

/-! A coarse bound on the actual paper statistics constant at dimension 13140. -/
namespace BstLean.Part266.Row13140
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13138 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13138 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13138 128 ≤ (13392 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13392 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13140) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13140 : ℕ))
    (by norm_num : (13140 : ℕ) ≤ 16384)
  have ht : paperTail256 13140 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13140 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13140 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13140 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13140 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13140 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13138 128 * √(2 / (13140 : ℝ)) *
      (√(13140 : ℝ) + paperT0 13140 + paperTail256 13140) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13140 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13140 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13140 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13138 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13138 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13140 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13140

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13140
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13140 (61 / 100) 165 (17 / (100 * 13140)) (26 / (10 * 13140)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13140 (61 / 100) 165 (17 / (100 * 13140)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (107564717 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1309768261 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1945168847 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13140 / 13140 * (61 / 100)) ^ 4 * inverseRadius8 (13140 - 1) /
            envelopeGap 13140 (61 / 100) 165 (17 / (100 * 13140)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13140

namespace BstLean.Part266.Row13140
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13140 165 ≤ (4208626411 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13140 165 ≤ (1404068831 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (337468447 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13140 165 ≤ (331026283 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 13140 165 ≤ (47103773 / 4000000000000000000)
  w2 : (tableEnvelope C).w2 13140 165 ≤ (430262637 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (107564717 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (107564717 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1309768261 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1945168847 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1798443 / 500000000) : ℝ) ≤ √(17 / (100 * 13140) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13140) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (518567057 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4523840081 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13140) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13140) ≤ (107626603 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13140) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13140 * (165 : ℝ) ^ 2 + 26 / (10 * 13140) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13140) : ℝ)) (tA 13140 * 165 ^ 2 + 26 / (10 * 13140)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1798443 / 500000000))) * ((107564717 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1798443 / 500000000)) ^ 3) * ((1309768261 / 1000000000000000000000000))) + ((1945168847 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1798443 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13140) : ℝ)) d.D d.V d.P (√(tA 13140) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1798443 / 500000000)) ^ 2 * (((518567057 / 250000000000000)) * ((4523840081 / 125000000000000000)))) + ((1945168847 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13140) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1798443 / 500000000)) * ((107564717 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13140) : ℝ)) (tA 13140 * 165 ^ 2 + 26 / (10 * 13140)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((107564717 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1798443 / 500000000)) ^ 2) * ((1309768261 / 1000000000000000000000000)) + ((1945168847 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13140) : ℝ)) (√(26 / (10 * 13140) : ℝ)) d.D d.V d.P (√(tA 13140) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1798443 / 500000000)) * (((518567057 / 250000000000000)) * ((4523840081 / 125000000000000000))) + ((1945168847 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13140) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((107564717 / 25000000000000000000) : ℝ) + ((1945168847 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13140

namespace BstLean.Part266.Row13140
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13140 165 ∧
    0 ≤ (tableEnvelope C).f1 13140 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13140 165 ∧
    0 ≤ (tableEnvelope C).w1 13140 165 ∧ 0 ≤ (tableEnvelope C).w2 13140 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13140 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13140 165 ∧ 0 ≤ d.f1 13140 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13140 165 ∧ 0 ≤ d.w1 13140 165 ∧ 0 ≤ d.w2 13140 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13140 ≤ 2 * (228 / 100 : ℝ) / 13140 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13140 ≤ 2 * (370 / 100 : ℝ) / 13140 := by
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
    (completeRAData (tableEnvelope C) 13140 165).locationBound 13140 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13140 165).energyBound 13140 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13140 165) (d.f1 13140 165) d.f2 ≤
      32 * (((4208626411 / 1000000000000000000) : ℝ) + (1404068831 / 1000000000000000000) + (337468447 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13140 165) (d.w1 13140 165)
      (d.w2 13140 165) ≤
      32 * (((331026283 / 20000000000000000000) : ℝ) + (47103773 / 4000000000000000000) + (430262637 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13140 165) (d.f1 13140 165) d.f2 ≤
      ((4208626411 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4208626411 / 1000000000000000000)) * ((1404068831 / 1000000000000000000)) * (126 / 100) +
      2 * (((1404068831 / 1000000000000000000)) ^ 2 + 2 * ((4208626411 / 1000000000000000000)) * ((337468447 / 1000000000000000000))) +
      6 * ((1404068831 / 1000000000000000000)) * ((337468447 / 1000000000000000000)) * (126 / 100) + 8 * ((337468447 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13140 165) (d.f1 13140 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13140 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13140 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13140 165) (d.f1 13140 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13140 165) (d.w1 13140 165) (d.w2 13140 165)
  have hwexpr0 : 0 ≤ d.w0 13140 165 + d.w1 13140 165 * √(π / 2) +
      2 * d.w2 13140 165 + energyR16 13140 *
      radiusPolynomialRoot16 (d.w0 13140 165) (d.w1 13140 165) (d.w2 13140 165) := by
    positivity
  constructor
  · change (13140 : ℝ) ^ 8 * (mA 13140 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13140 165) (d.f1 13140 165) d.f2 + locationR16 13140 *
        radiusPolynomialRoot16 (d.f0 13140 165) (d.f1 13140 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13140 : ℝ) ^ 8 * (mA 13140 : ℝ) ^ 8 *
        ((((4208626411 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4208626411 / 1000000000000000000)) * ((1404068831 / 1000000000000000000)) * (126 / 100) +
          2 * (((1404068831 / 1000000000000000000)) ^ 2 + 2 * ((4208626411 / 1000000000000000000)) * ((337468447 / 1000000000000000000))) +
          6 * ((1404068831 / 1000000000000000000)) * ((337468447 / 1000000000000000000)) * (126 / 100) + 8 * ((337468447 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13140) *
          (32 * (((4208626411 / 1000000000000000000) : ℝ) + (1404068831 / 1000000000000000000) + (337468447 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13140 : ℝ) ^ 16 *
      (d.w0 13140 165 + d.w1 13140 165 * √(π / 2) + 2 * d.w2 13140 165 +
        energyR16 13140 * radiusPolynomialRoot16 (d.w0 13140 165) (d.w1 13140 165)
          (d.w2 13140 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13140 : ℝ) ^ 16 *
        (((331026283 / 20000000000000000000) : ℝ) + ((47103773 / 4000000000000000000)) * (126 / 100) + 2 * ((430262637 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13140) *
          (32 * (((331026283 / 20000000000000000000) : ℝ) + (47103773 / 4000000000000000000) + (430262637 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13140

/-! A coarse bound on the actual paper statistics constant at dimension 13141. -/
namespace BstLean.Part266.Row13141
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13139 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13139 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13139 128 ≤ (13393 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13393 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13141) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13141 : ℕ))
    (by norm_num : (13141 : ℕ) ≤ 16384)
  have ht : paperTail256 13141 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13141 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13141 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13141 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13141 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13141 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13139 128 * √(2 / (13141 : ℝ)) *
      (√(13141 : ℝ) + paperT0 13141 + paperTail256 13141) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13141 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13141 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13141 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13139 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13139 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13141 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13141

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13141
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13141 (61 / 100) 165 (17 / (100 * 13141)) (26 / (10 * 13141)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13141 (61 / 100) 165 (17 / (100 * 13141)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (86032129 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (130936961 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3887947889 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13141 / 13141 * (61 / 100)) ^ 4 * inverseRadius8 (13141 - 1) /
            envelopeGap 13141 (61 / 100) 165 (17 / (100 * 13141)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13141

namespace BstLean.Part266.Row13141
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13141 165 ≤ (1051955709 / 250000000000000000)
  f1 : (tableEnvelope C).f1 13141 165 ≤ (701900521 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (84351041 / 250000000000000000)
  w0 : (tableEnvelope C).w0 13141 165 ≤ (206844123 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 13141 165 ≤ (1177325213 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13141 165 ≤ (107541103 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (86032129 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (86032129 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (130936961 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3887947889 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((14387 / 4000000) : ℝ) ≤ √(17 / (100 * 13141) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13141) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2074031449 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9046303147 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13141) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13141) ≤ (107618413 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13141) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13141 * (165 : ℝ) ^ 2 + 26 / (10 * 13141) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13141) : ℝ)) (tA 13141 * 165 ^ 2 + 26 / (10 * 13141)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((14387 / 4000000))) * ((86032129 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((14387 / 4000000)) ^ 3) * ((130936961 / 100000000000000000000000))) + ((3887947889 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((14387 / 4000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13141) : ℝ)) d.D d.V d.P (√(tA 13141) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((14387 / 4000000)) ^ 2 * (((2074031449 / 1000000000000000)) * ((9046303147 / 250000000000000000)))) + ((3887947889 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13141) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((14387 / 4000000)) * ((86032129 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13141) : ℝ)) (tA 13141 * 165 ^ 2 + 26 / (10 * 13141)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((86032129 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((14387 / 4000000)) ^ 2) * ((130936961 / 100000000000000000000000)) + ((3887947889 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13141) : ℝ)) (√(26 / (10 * 13141) : ℝ)) d.D d.V d.P (√(tA 13141) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((14387 / 4000000)) * (((2074031449 / 1000000000000000)) * ((9046303147 / 250000000000000000))) + ((3887947889 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13141) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((86032129 / 20000000000000000000) : ℝ) + ((3887947889 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13141

namespace BstLean.Part266.Row13141
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13141 165 ∧
    0 ≤ (tableEnvelope C).f1 13141 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13141 165 ∧
    0 ≤ (tableEnvelope C).w1 13141 165 ∧ 0 ≤ (tableEnvelope C).w2 13141 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13141 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13141 165 ∧ 0 ≤ d.f1 13141 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13141 165 ∧ 0 ≤ d.w1 13141 165 ∧ 0 ≤ d.w2 13141 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13141 ≤ 2 * (228 / 100 : ℝ) / 13141 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13141 ≤ 2 * (370 / 100 : ℝ) / 13141 := by
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
    (completeRAData (tableEnvelope C) 13141 165).locationBound 13141 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13141 165).energyBound 13141 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13141 165) (d.f1 13141 165) d.f2 ≤
      32 * (((1051955709 / 250000000000000000) : ℝ) + (701900521 / 500000000000000000) + (84351041 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13141 165) (d.w1 13141 165)
      (d.w2 13141 165) ≤
      32 * (((206844123 / 12500000000000000000) : ℝ) + (1177325213 / 100000000000000000000) + (107541103 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13141 165) (d.f1 13141 165) d.f2 ≤
      ((1051955709 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1051955709 / 250000000000000000)) * ((701900521 / 500000000000000000)) * (126 / 100) +
      2 * (((701900521 / 500000000000000000)) ^ 2 + 2 * ((1051955709 / 250000000000000000)) * ((84351041 / 250000000000000000))) +
      6 * ((701900521 / 500000000000000000)) * ((84351041 / 250000000000000000)) * (126 / 100) + 8 * ((84351041 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13141 165) (d.f1 13141 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13141 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13141 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13141 165) (d.f1 13141 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13141 165) (d.w1 13141 165) (d.w2 13141 165)
  have hwexpr0 : 0 ≤ d.w0 13141 165 + d.w1 13141 165 * √(π / 2) +
      2 * d.w2 13141 165 + energyR16 13141 *
      radiusPolynomialRoot16 (d.w0 13141 165) (d.w1 13141 165) (d.w2 13141 165) := by
    positivity
  constructor
  · change (13141 : ℝ) ^ 8 * (mA 13141 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13141 165) (d.f1 13141 165) d.f2 + locationR16 13141 *
        radiusPolynomialRoot16 (d.f0 13141 165) (d.f1 13141 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13141 : ℝ) ^ 8 * (mA 13141 : ℝ) ^ 8 *
        ((((1051955709 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1051955709 / 250000000000000000)) * ((701900521 / 500000000000000000)) * (126 / 100) +
          2 * (((701900521 / 500000000000000000)) ^ 2 + 2 * ((1051955709 / 250000000000000000)) * ((84351041 / 250000000000000000))) +
          6 * ((701900521 / 500000000000000000)) * ((84351041 / 250000000000000000)) * (126 / 100) + 8 * ((84351041 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13141) *
          (32 * (((1051955709 / 250000000000000000) : ℝ) + (701900521 / 500000000000000000) + (84351041 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13141 : ℝ) ^ 16 *
      (d.w0 13141 165 + d.w1 13141 165 * √(π / 2) + 2 * d.w2 13141 165 +
        energyR16 13141 * radiusPolynomialRoot16 (d.w0 13141 165) (d.w1 13141 165)
          (d.w2 13141 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13141 : ℝ) ^ 16 *
        (((206844123 / 12500000000000000000) : ℝ) + ((1177325213 / 100000000000000000000)) * (126 / 100) + 2 * ((107541103 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13141) *
          (32 * (((206844123 / 12500000000000000000) : ℝ) + (1177325213 / 100000000000000000000) + (107541103 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13141

/-! A coarse bound on the actual paper statistics constant at dimension 13142. -/
namespace BstLean.Part266.Row13142
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13140 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13140 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13140 128 ≤ (13394 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13394 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13142) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13142 : ℕ))
    (by norm_num : (13142 : ℕ) ≤ 16384)
  have ht : paperTail256 13142 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13142 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13142 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13142 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13142 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13142 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13140 128 * √(2 / (13142 : ℝ)) *
      (√(13142 : ℝ) + paperT0 13142 + paperTail256 13142) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13142 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13142 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13142 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13140 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13140 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13142 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13142

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13142
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13142 (61 / 100) 165 (17 / (100 * 13142)) (26 / (10 * 13142)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13142 (61 / 100) 165 (17 / (100 * 13142)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (430062453 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (130897111 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1942779869 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13142 / 13142 * (61 / 100)) ^ 4 * inverseRadius8 (13142 - 1) /
            envelopeGap 13142 (61 / 100) 165 (17 / (100 * 13142)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13142

namespace BstLean.Part266.Row13142
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13142 165 ≤ (525877863 / 125000000000000000)
  f1 : (tableEnvelope C).f1 13142 165 ≤ (701767059 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (67467999 / 200000000000000000)
  w0 : (tableEnvelope C).w0 13142 165 ≤ (1654375359 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13142 165 ≤ (1177056517 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13142 165 ≤ (430066217 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (430062453 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (430062453 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (130897111 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1942779869 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3596613 / 1000000000) : ℝ) ≤ √(17 / (100 * 13142) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13142) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1036897359 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (2261231611 / 62500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13142) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13142) ≤ (6725639 / 62500000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13142) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13142 * (165 : ℝ) ^ 2 + 26 / (10 * 13142) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13142) : ℝ)) (tA 13142 * 165 ^ 2 + 26 / (10 * 13142)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3596613 / 1000000000))) * ((430062453 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3596613 / 1000000000)) ^ 3) * ((130897111 / 100000000000000000000000))) + ((1942779869 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3596613 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13142) : ℝ)) d.D d.V d.P (√(tA 13142) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3596613 / 1000000000)) ^ 2 * (((1036897359 / 500000000000000)) * ((2261231611 / 62500000000000000)))) + ((1942779869 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13142) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3596613 / 1000000000)) * ((430062453 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13142) : ℝ)) (tA 13142 * 165 ^ 2 + 26 / (10 * 13142)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((430062453 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3596613 / 1000000000)) ^ 2) * ((130897111 / 100000000000000000000000)) + ((1942779869 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13142) : ℝ)) (√(26 / (10 * 13142) : ℝ)) d.D d.V d.P (√(tA 13142) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3596613 / 1000000000)) * (((1036897359 / 500000000000000)) * ((2261231611 / 62500000000000000))) + ((1942779869 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13142) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((430062453 / 100000000000000000000) : ℝ) + ((1942779869 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13142

namespace BstLean.Part266.Row13142
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13142 165 ∧
    0 ≤ (tableEnvelope C).f1 13142 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13142 165 ∧
    0 ≤ (tableEnvelope C).w1 13142 165 ∧ 0 ≤ (tableEnvelope C).w2 13142 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13142 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13142 165 ∧ 0 ≤ d.f1 13142 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13142 165 ∧ 0 ≤ d.w1 13142 165 ∧ 0 ≤ d.w2 13142 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13142 ≤ 2 * (228 / 100 : ℝ) / 13142 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13142 ≤ 2 * (370 / 100 : ℝ) / 13142 := by
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
    (completeRAData (tableEnvelope C) 13142 165).locationBound 13142 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13142 165).energyBound 13142 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13142 165) (d.f1 13142 165) d.f2 ≤
      32 * (((525877863 / 125000000000000000) : ℝ) + (701767059 / 500000000000000000) + (67467999 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13142 165) (d.w1 13142 165)
      (d.w2 13142 165) ≤
      32 * (((1654375359 / 100000000000000000000) : ℝ) + (1177056517 / 100000000000000000000) + (430066217 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13142 165) (d.f1 13142 165) d.f2 ≤
      ((525877863 / 125000000000000000) : ℝ) ^ 2 + 2 * ((525877863 / 125000000000000000)) * ((701767059 / 500000000000000000)) * (126 / 100) +
      2 * (((701767059 / 500000000000000000)) ^ 2 + 2 * ((525877863 / 125000000000000000)) * ((67467999 / 200000000000000000))) +
      6 * ((701767059 / 500000000000000000)) * ((67467999 / 200000000000000000)) * (126 / 100) + 8 * ((67467999 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13142 165) (d.f1 13142 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13142 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13142 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13142 165) (d.f1 13142 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13142 165) (d.w1 13142 165) (d.w2 13142 165)
  have hwexpr0 : 0 ≤ d.w0 13142 165 + d.w1 13142 165 * √(π / 2) +
      2 * d.w2 13142 165 + energyR16 13142 *
      radiusPolynomialRoot16 (d.w0 13142 165) (d.w1 13142 165) (d.w2 13142 165) := by
    positivity
  constructor
  · change (13142 : ℝ) ^ 8 * (mA 13142 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13142 165) (d.f1 13142 165) d.f2 + locationR16 13142 *
        radiusPolynomialRoot16 (d.f0 13142 165) (d.f1 13142 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13142 : ℝ) ^ 8 * (mA 13142 : ℝ) ^ 8 *
        ((((525877863 / 125000000000000000) : ℝ) ^ 2 + 2 * ((525877863 / 125000000000000000)) * ((701767059 / 500000000000000000)) * (126 / 100) +
          2 * (((701767059 / 500000000000000000)) ^ 2 + 2 * ((525877863 / 125000000000000000)) * ((67467999 / 200000000000000000))) +
          6 * ((701767059 / 500000000000000000)) * ((67467999 / 200000000000000000)) * (126 / 100) + 8 * ((67467999 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13142) *
          (32 * (((525877863 / 125000000000000000) : ℝ) + (701767059 / 500000000000000000) + (67467999 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13142 : ℝ) ^ 16 *
      (d.w0 13142 165 + d.w1 13142 165 * √(π / 2) + 2 * d.w2 13142 165 +
        energyR16 13142 * radiusPolynomialRoot16 (d.w0 13142 165) (d.w1 13142 165)
          (d.w2 13142 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13142 : ℝ) ^ 16 *
        (((1654375359 / 100000000000000000000) : ℝ) + ((1177056517 / 100000000000000000000)) * (126 / 100) + 2 * ((430066217 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13142) *
          (32 * (((1654375359 / 100000000000000000000) : ℝ) + (1177056517 / 100000000000000000000) + (430066217 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13142

/-! A coarse bound on the actual paper statistics constant at dimension 13143. -/
namespace BstLean.Part266.Row13143
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13141 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13141 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13141 128 ≤ (13395 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13395 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13143) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13143 : ℕ))
    (by norm_num : (13143 : ℕ) ≤ 16384)
  have ht : paperTail256 13143 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13143 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13143 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13143 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13143 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13143 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13141 128 * √(2 / (13143 : ℝ)) *
      (√(13143 : ℝ) + paperT0 13143 + paperTail256 13143) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13143 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13143 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13143 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13141 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13141 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13143 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13143

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13143
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13143 (61 / 100) 165 (17 / (100 * 13143)) (26 / (10 * 13143)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13143 (61 / 100) 165 (17 / (100 * 13143)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (42996429 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (654286381 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1941586619 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13143 / 13143 * (61 / 100)) ^ 4 * inverseRadius8 (13143 - 1) /
            envelopeGap 13143 (61 / 100) 165 (17 / (100 * 13143)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13143

namespace BstLean.Part266.Row13143
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13143 165 ≤ (2103111619 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13143 165 ≤ (1403267277 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (337275843 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13143 165 ≤ (82699893 / 5000000000000000000)
  w1 : (tableEnvelope C).w1 13143 165 ≤ (1176787907 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13143 165 ≤ (107492013 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (42996429 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (42996429 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (654286381 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1941586619 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((899119 / 250000000) : ℝ) ≤ √(17 / (100 * 13143) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13143) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (207355803 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36174200227 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13143) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13143) ≤ (107602037 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13143) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13143 * (165 : ℝ) ^ 2 + 26 / (10 * 13143) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13143) : ℝ)) (tA 13143 * 165 ^ 2 + 26 / (10 * 13143)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((899119 / 250000000))) * ((42996429 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((899119 / 250000000)) ^ 3) * ((654286381 / 500000000000000000000000))) + ((1941586619 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((899119 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13143) : ℝ)) d.D d.V d.P (√(tA 13143) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((899119 / 250000000)) ^ 2 * (((207355803 / 100000000000000)) * ((36174200227 / 1000000000000000000)))) + ((1941586619 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13143) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((899119 / 250000000)) * ((42996429 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13143) : ℝ)) (tA 13143 * 165 ^ 2 + 26 / (10 * 13143)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((42996429 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((899119 / 250000000)) ^ 2) * ((654286381 / 500000000000000000000000)) + ((1941586619 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13143) : ℝ)) (√(26 / (10 * 13143) : ℝ)) d.D d.V d.P (√(tA 13143) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((899119 / 250000000)) * (((207355803 / 100000000000000)) * ((36174200227 / 1000000000000000000))) + ((1941586619 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13143) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((42996429 / 10000000000000000000) : ℝ) + ((1941586619 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13143

namespace BstLean.Part266.Row13143
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13143 165 ∧
    0 ≤ (tableEnvelope C).f1 13143 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13143 165 ∧
    0 ≤ (tableEnvelope C).w1 13143 165 ∧ 0 ≤ (tableEnvelope C).w2 13143 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13143 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13143 165 ∧ 0 ≤ d.f1 13143 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13143 165 ∧ 0 ≤ d.w1 13143 165 ∧ 0 ≤ d.w2 13143 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13143 ≤ 2 * (228 / 100 : ℝ) / 13143 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13143 ≤ 2 * (370 / 100 : ℝ) / 13143 := by
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
    (completeRAData (tableEnvelope C) 13143 165).locationBound 13143 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13143 165).energyBound 13143 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13143 165) (d.f1 13143 165) d.f2 ≤
      32 * (((2103111619 / 500000000000000000) : ℝ) + (1403267277 / 1000000000000000000) + (337275843 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13143 165) (d.w1 13143 165)
      (d.w2 13143 165) ≤
      32 * (((82699893 / 5000000000000000000) : ℝ) + (1176787907 / 100000000000000000000) + (107492013 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13143 165) (d.f1 13143 165) d.f2 ≤
      ((2103111619 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2103111619 / 500000000000000000)) * ((1403267277 / 1000000000000000000)) * (126 / 100) +
      2 * (((1403267277 / 1000000000000000000)) ^ 2 + 2 * ((2103111619 / 500000000000000000)) * ((337275843 / 1000000000000000000))) +
      6 * ((1403267277 / 1000000000000000000)) * ((337275843 / 1000000000000000000)) * (126 / 100) + 8 * ((337275843 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13143 165) (d.f1 13143 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13143 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13143 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13143 165) (d.f1 13143 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13143 165) (d.w1 13143 165) (d.w2 13143 165)
  have hwexpr0 : 0 ≤ d.w0 13143 165 + d.w1 13143 165 * √(π / 2) +
      2 * d.w2 13143 165 + energyR16 13143 *
      radiusPolynomialRoot16 (d.w0 13143 165) (d.w1 13143 165) (d.w2 13143 165) := by
    positivity
  constructor
  · change (13143 : ℝ) ^ 8 * (mA 13143 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13143 165) (d.f1 13143 165) d.f2 + locationR16 13143 *
        radiusPolynomialRoot16 (d.f0 13143 165) (d.f1 13143 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13143 : ℝ) ^ 8 * (mA 13143 : ℝ) ^ 8 *
        ((((2103111619 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2103111619 / 500000000000000000)) * ((1403267277 / 1000000000000000000)) * (126 / 100) +
          2 * (((1403267277 / 1000000000000000000)) ^ 2 + 2 * ((2103111619 / 500000000000000000)) * ((337275843 / 1000000000000000000))) +
          6 * ((1403267277 / 1000000000000000000)) * ((337275843 / 1000000000000000000)) * (126 / 100) + 8 * ((337275843 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13143) *
          (32 * (((2103111619 / 500000000000000000) : ℝ) + (1403267277 / 1000000000000000000) + (337275843 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13143 : ℝ) ^ 16 *
      (d.w0 13143 165 + d.w1 13143 165 * √(π / 2) + 2 * d.w2 13143 165 +
        energyR16 13143 * radiusPolynomialRoot16 (d.w0 13143 165) (d.w1 13143 165)
          (d.w2 13143 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13143 : ℝ) ^ 16 *
        (((82699893 / 5000000000000000000) : ℝ) + ((1176787907 / 100000000000000000000)) * (126 / 100) + 2 * ((107492013 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13143) *
          (32 * (((82699893 / 5000000000000000000) : ℝ) + (1176787907 / 100000000000000000000) + (107492013 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13143

/-! A coarse bound on the actual paper statistics constant at dimension 13144. -/
namespace BstLean.Part266.Row13144
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13142 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13142 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13142 128 ≤ (13396 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13396 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13144) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13144 : ℕ))
    (by norm_num : (13144 : ℕ) ≤ 16384)
  have ht : paperTail256 13144 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13144 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13144 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13144 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13144 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13144 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13142 128 * √(2 / (13144 : ℝ)) *
      (√(13144 : ℝ) + paperT0 13144 + paperTail256 13144) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13144 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13144 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13144 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13142 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13142 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13144 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13144

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13144
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13144 (61 / 100) 165 (17 / (100 * 13144)) (26 / (10 * 13144)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13144 (61 / 100) 165 (17 / (100 * 13144)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (429866157 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (654087283 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (970197097 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13144 / 13144 * (61 / 100)) ^ 4 * inverseRadius8 (13144 - 1) /
            envelopeGap 13144 (61 / 100) 165 (17 / (100 * 13144)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13144

namespace BstLean.Part266.Row13144
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13144 165 ≤ (4205423839 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13144 165 ≤ (1403000519 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (33721171 / 100000000000000000)
  w0 : (tableEnvelope C).w0 13144 165 ≤ (826810243 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13144 165 ≤ (1176519383 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13144 165 ≤ (429869917 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (429866157 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (429866157 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (654087283 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (970197097 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3596339 / 1000000000) : ℝ) ≤ √(17 / (100 * 13144) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13144) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2073321387 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1808434797 / 50000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13144) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13144) ≤ (2151877 / 20000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13144) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13144 * (165 : ℝ) ^ 2 + 26 / (10 * 13144) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13144) : ℝ)) (tA 13144 * 165 ^ 2 + 26 / (10 * 13144)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3596339 / 1000000000))) * ((429866157 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3596339 / 1000000000)) ^ 3) * ((654087283 / 500000000000000000000000))) + ((970197097 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3596339 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13144) : ℝ)) d.D d.V d.P (√(tA 13144) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3596339 / 1000000000)) ^ 2 * (((2073321387 / 1000000000000000)) * ((1808434797 / 50000000000000000)))) + ((970197097 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13144) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3596339 / 1000000000)) * ((429866157 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13144) : ℝ)) (tA 13144 * 165 ^ 2 + 26 / (10 * 13144)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((429866157 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3596339 / 1000000000)) ^ 2) * ((654087283 / 500000000000000000000000)) + ((970197097 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13144) : ℝ)) (√(26 / (10 * 13144) : ℝ)) d.D d.V d.P (√(tA 13144) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3596339 / 1000000000)) * (((2073321387 / 1000000000000000)) * ((1808434797 / 50000000000000000))) + ((970197097 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13144) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((429866157 / 100000000000000000000) : ℝ) + ((970197097 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13144

namespace BstLean.Part266.Row13144
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13144 165 ∧
    0 ≤ (tableEnvelope C).f1 13144 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13144 165 ∧
    0 ≤ (tableEnvelope C).w1 13144 165 ∧ 0 ≤ (tableEnvelope C).w2 13144 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13144 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13144 165 ∧ 0 ≤ d.f1 13144 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13144 165 ∧ 0 ≤ d.w1 13144 165 ∧ 0 ≤ d.w2 13144 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13144 ≤ 2 * (228 / 100 : ℝ) / 13144 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13144 ≤ 2 * (370 / 100 : ℝ) / 13144 := by
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
    (completeRAData (tableEnvelope C) 13144 165).locationBound 13144 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13144 165).energyBound 13144 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13144 165) (d.f1 13144 165) d.f2 ≤
      32 * (((4205423839 / 1000000000000000000) : ℝ) + (1403000519 / 1000000000000000000) + (33721171 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13144 165) (d.w1 13144 165)
      (d.w2 13144 165) ≤
      32 * (((826810243 / 50000000000000000000) : ℝ) + (1176519383 / 100000000000000000000) + (429869917 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13144 165) (d.f1 13144 165) d.f2 ≤
      ((4205423839 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4205423839 / 1000000000000000000)) * ((1403000519 / 1000000000000000000)) * (126 / 100) +
      2 * (((1403000519 / 1000000000000000000)) ^ 2 + 2 * ((4205423839 / 1000000000000000000)) * ((33721171 / 100000000000000000))) +
      6 * ((1403000519 / 1000000000000000000)) * ((33721171 / 100000000000000000)) * (126 / 100) + 8 * ((33721171 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13144 165) (d.f1 13144 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13144 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13144 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13144 165) (d.f1 13144 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13144 165) (d.w1 13144 165) (d.w2 13144 165)
  have hwexpr0 : 0 ≤ d.w0 13144 165 + d.w1 13144 165 * √(π / 2) +
      2 * d.w2 13144 165 + energyR16 13144 *
      radiusPolynomialRoot16 (d.w0 13144 165) (d.w1 13144 165) (d.w2 13144 165) := by
    positivity
  constructor
  · change (13144 : ℝ) ^ 8 * (mA 13144 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13144 165) (d.f1 13144 165) d.f2 + locationR16 13144 *
        radiusPolynomialRoot16 (d.f0 13144 165) (d.f1 13144 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13144 : ℝ) ^ 8 * (mA 13144 : ℝ) ^ 8 *
        ((((4205423839 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4205423839 / 1000000000000000000)) * ((1403000519 / 1000000000000000000)) * (126 / 100) +
          2 * (((1403000519 / 1000000000000000000)) ^ 2 + 2 * ((4205423839 / 1000000000000000000)) * ((33721171 / 100000000000000000))) +
          6 * ((1403000519 / 1000000000000000000)) * ((33721171 / 100000000000000000)) * (126 / 100) + 8 * ((33721171 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13144) *
          (32 * (((4205423839 / 1000000000000000000) : ℝ) + (1403000519 / 1000000000000000000) + (33721171 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13144 : ℝ) ^ 16 *
      (d.w0 13144 165 + d.w1 13144 165 * √(π / 2) + 2 * d.w2 13144 165 +
        energyR16 13144 * radiusPolynomialRoot16 (d.w0 13144 165) (d.w1 13144 165)
          (d.w2 13144 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13144 : ℝ) ^ 16 *
        (((826810243 / 50000000000000000000) : ℝ) + ((1176519383 / 100000000000000000000)) * (126 / 100) + 2 * ((429869917 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13144) *
          (32 * (((826810243 / 50000000000000000000) : ℝ) + (1176519383 / 100000000000000000000) + (429869917 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13144

/-! A coarse bound on the actual paper statistics constant at dimension 13145. -/
namespace BstLean.Part266.Row13145
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13143 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13143 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13143 128 ≤ (13397 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13397 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13145) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13145 : ℕ))
    (by norm_num : (13145 : ℕ) ≤ 16384)
  have ht : paperTail256 13145 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13145 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13145 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13145 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13145 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13145 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13143 128 * √(2 / (13145 : ℝ)) *
      (√(13145 : ℝ) + paperT0 13145 + paperTail256 13145) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13145 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13145 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13145 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13143 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13143 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13145 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13145

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13145
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13145 (61 / 100) 165 (17 / (100 * 13145)) (26 / (10 * 13145)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13145 (61 / 100) 165 (17 / (100 * 13145)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (214884027 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1307776521 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (969601297 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13145 / 13145 * (61 / 100)) ^ 4 * inverseRadius8 (13145 - 1) /
            envelopeGap 13145 (61 / 100) 165 (17 / (100 * 13145)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13145

namespace BstLean.Part266.Row13145
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13145 165 ≤ (840924941 / 200000000000000000)
  f1 : (tableEnvelope C).f1 13145 165 ≤ (350683461 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (84286899 / 250000000000000000)
  w0 : (tableEnvelope C).w0 13145 165 ≤ (826621619 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13145 165 ≤ (588125473 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13145 165 ≤ (429771811 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (214884027 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (214884027 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1307776521 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (969601297 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1798101 / 500000000) : ℝ) ≤ √(17 / (100 * 13145) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13145) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2073084789 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4520399113 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13145) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13145) ≤ (21517133 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13145) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13145 * (165 : ℝ) ^ 2 + 26 / (10 * 13145) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13145) : ℝ)) (tA 13145 * 165 ^ 2 + 26 / (10 * 13145)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1798101 / 500000000))) * ((214884027 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1798101 / 500000000)) ^ 3) * ((1307776521 / 1000000000000000000000000))) + ((969601297 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1798101 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13145) : ℝ)) d.D d.V d.P (√(tA 13145) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1798101 / 500000000)) ^ 2 * (((2073084789 / 1000000000000000)) * ((4520399113 / 125000000000000000)))) + ((969601297 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13145) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1798101 / 500000000)) * ((214884027 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13145) : ℝ)) (tA 13145 * 165 ^ 2 + 26 / (10 * 13145)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((214884027 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1798101 / 500000000)) ^ 2) * ((1307776521 / 1000000000000000000000000)) + ((969601297 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13145) : ℝ)) (√(26 / (10 * 13145) : ℝ)) d.D d.V d.P (√(tA 13145) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1798101 / 500000000)) * (((2073084789 / 1000000000000000)) * ((4520399113 / 125000000000000000))) + ((969601297 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13145) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((214884027 / 50000000000000000000) : ℝ) + ((969601297 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13145

namespace BstLean.Part266.Row13145
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13145 165 ∧
    0 ≤ (tableEnvelope C).f1 13145 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13145 165 ∧
    0 ≤ (tableEnvelope C).w1 13145 165 ∧ 0 ≤ (tableEnvelope C).w2 13145 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13145 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13145 165 ∧ 0 ≤ d.f1 13145 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13145 165 ∧ 0 ≤ d.w1 13145 165 ∧ 0 ≤ d.w2 13145 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13145 ≤ 2 * (228 / 100 : ℝ) / 13145 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13145 ≤ 2 * (370 / 100 : ℝ) / 13145 := by
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
    (completeRAData (tableEnvelope C) 13145 165).locationBound 13145 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13145 165).energyBound 13145 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13145 165) (d.f1 13145 165) d.f2 ≤
      32 * (((840924941 / 200000000000000000) : ℝ) + (350683461 / 250000000000000000) + (84286899 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13145 165) (d.w1 13145 165)
      (d.w2 13145 165) ≤
      32 * (((826621619 / 50000000000000000000) : ℝ) + (588125473 / 50000000000000000000) + (429771811 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13145 165) (d.f1 13145 165) d.f2 ≤
      ((840924941 / 200000000000000000) : ℝ) ^ 2 + 2 * ((840924941 / 200000000000000000)) * ((350683461 / 250000000000000000)) * (126 / 100) +
      2 * (((350683461 / 250000000000000000)) ^ 2 + 2 * ((840924941 / 200000000000000000)) * ((84286899 / 250000000000000000))) +
      6 * ((350683461 / 250000000000000000)) * ((84286899 / 250000000000000000)) * (126 / 100) + 8 * ((84286899 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13145 165) (d.f1 13145 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13145 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13145 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13145 165) (d.f1 13145 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13145 165) (d.w1 13145 165) (d.w2 13145 165)
  have hwexpr0 : 0 ≤ d.w0 13145 165 + d.w1 13145 165 * √(π / 2) +
      2 * d.w2 13145 165 + energyR16 13145 *
      radiusPolynomialRoot16 (d.w0 13145 165) (d.w1 13145 165) (d.w2 13145 165) := by
    positivity
  constructor
  · change (13145 : ℝ) ^ 8 * (mA 13145 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13145 165) (d.f1 13145 165) d.f2 + locationR16 13145 *
        radiusPolynomialRoot16 (d.f0 13145 165) (d.f1 13145 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13145 : ℝ) ^ 8 * (mA 13145 : ℝ) ^ 8 *
        ((((840924941 / 200000000000000000) : ℝ) ^ 2 + 2 * ((840924941 / 200000000000000000)) * ((350683461 / 250000000000000000)) * (126 / 100) +
          2 * (((350683461 / 250000000000000000)) ^ 2 + 2 * ((840924941 / 200000000000000000)) * ((84286899 / 250000000000000000))) +
          6 * ((350683461 / 250000000000000000)) * ((84286899 / 250000000000000000)) * (126 / 100) + 8 * ((84286899 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13145) *
          (32 * (((840924941 / 200000000000000000) : ℝ) + (350683461 / 250000000000000000) + (84286899 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13145 : ℝ) ^ 16 *
      (d.w0 13145 165 + d.w1 13145 165 * √(π / 2) + 2 * d.w2 13145 165 +
        energyR16 13145 * radiusPolynomialRoot16 (d.w0 13145 165) (d.w1 13145 165)
          (d.w2 13145 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13145 : ℝ) ^ 16 *
        (((826621619 / 50000000000000000000) : ℝ) + ((588125473 / 50000000000000000000)) * (126 / 100) + 2 * ((429771811 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13145) *
          (32 * (((826621619 / 50000000000000000000) : ℝ) + (588125473 / 50000000000000000000) + (429771811 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13145

/-! A coarse bound on the actual paper statistics constant at dimension 13146. -/
namespace BstLean.Part266.Row13146
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13144 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13144 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13144 128 ≤ (13398 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13398 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13146) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13146 : ℕ))
    (by norm_num : (13146 : ℕ) ≤ 16384)
  have ht : paperTail256 13146 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13146 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13146 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13146 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13146 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13146 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13144 128 * √(2 / (13146 : ℝ)) *
      (√(13146 : ℝ) + paperT0 13146 + paperTail256 13146) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13146 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13146 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13146 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13144 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13144 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13146 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13146

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13146
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13146 (61 / 100) 165 (17 / (100 * 13146)) (26 / (10 * 13146)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13146 (61 / 100) 165 (17 / (100 * 13146)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (21483499 / 5000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (326844657 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (969005909 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13146 / 13146 * (61 / 100)) ^ 4 * inverseRadius8 (13146 - 1) /
            envelopeGap 13146 (61 / 100) 165 (17 / (100 * 13146)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13146

namespace BstLean.Part266.Row13146
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13146 165 ≤ (4203825837 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13146 165 ≤ (350616813 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (674167 / 2000000000000000)
  w0 : (tableEnvelope C).w0 13146 165 ≤ (330573223 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 13146 165 ≤ (235196519 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 13146 165 ≤ (85934747 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (21483499 / 5000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (21483499 / 5000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (326844657 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (969005909 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((719213 / 200000000) : ℝ) ≤ √(17 / (100 * 13146) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13146) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1036424117 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36157691133 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13146) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13146) ≤ (107577481 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13146) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13146 * (165 : ℝ) ^ 2 + 26 / (10 * 13146) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13146) : ℝ)) (tA 13146 * 165 ^ 2 + 26 / (10 * 13146)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((719213 / 200000000))) * ((21483499 / 5000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((719213 / 200000000)) ^ 3) * ((326844657 / 250000000000000000000000))) + ((969005909 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((719213 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13146) : ℝ)) d.D d.V d.P (√(tA 13146) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((719213 / 200000000)) ^ 2 * (((1036424117 / 500000000000000)) * ((36157691133 / 1000000000000000000)))) + ((969005909 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13146) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((719213 / 200000000)) * ((21483499 / 5000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13146) : ℝ)) (tA 13146 * 165 ^ 2 + 26 / (10 * 13146)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((21483499 / 5000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((719213 / 200000000)) ^ 2) * ((326844657 / 250000000000000000000000)) + ((969005909 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13146) : ℝ)) (√(26 / (10 * 13146) : ℝ)) d.D d.V d.P (√(tA 13146) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((719213 / 200000000)) * (((1036424117 / 500000000000000)) * ((36157691133 / 1000000000000000000))) + ((969005909 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13146) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((21483499 / 5000000000000000000) : ℝ) + ((969005909 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13146

namespace BstLean.Part266.Row13146
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13146 165 ∧
    0 ≤ (tableEnvelope C).f1 13146 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13146 165 ∧
    0 ≤ (tableEnvelope C).w1 13146 165 ∧ 0 ≤ (tableEnvelope C).w2 13146 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13146 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13146 165 ∧ 0 ≤ d.f1 13146 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13146 165 ∧ 0 ≤ d.w1 13146 165 ∧ 0 ≤ d.w2 13146 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13146 ≤ 2 * (228 / 100 : ℝ) / 13146 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13146 ≤ 2 * (370 / 100 : ℝ) / 13146 := by
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
    (completeRAData (tableEnvelope C) 13146 165).locationBound 13146 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13146 165).energyBound 13146 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13146 165) (d.f1 13146 165) d.f2 ≤
      32 * (((4203825837 / 1000000000000000000) : ℝ) + (350616813 / 250000000000000000) + (674167 / 2000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13146 165) (d.w1 13146 165)
      (d.w2 13146 165) ≤
      32 * (((330573223 / 20000000000000000000) : ℝ) + (235196519 / 20000000000000000000) + (85934747 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13146 165) (d.f1 13146 165) d.f2 ≤
      ((4203825837 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4203825837 / 1000000000000000000)) * ((350616813 / 250000000000000000)) * (126 / 100) +
      2 * (((350616813 / 250000000000000000)) ^ 2 + 2 * ((4203825837 / 1000000000000000000)) * ((674167 / 2000000000000000))) +
      6 * ((350616813 / 250000000000000000)) * ((674167 / 2000000000000000)) * (126 / 100) + 8 * ((674167 / 2000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13146 165) (d.f1 13146 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13146 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13146 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13146 165) (d.f1 13146 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13146 165) (d.w1 13146 165) (d.w2 13146 165)
  have hwexpr0 : 0 ≤ d.w0 13146 165 + d.w1 13146 165 * √(π / 2) +
      2 * d.w2 13146 165 + energyR16 13146 *
      radiusPolynomialRoot16 (d.w0 13146 165) (d.w1 13146 165) (d.w2 13146 165) := by
    positivity
  constructor
  · change (13146 : ℝ) ^ 8 * (mA 13146 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13146 165) (d.f1 13146 165) d.f2 + locationR16 13146 *
        radiusPolynomialRoot16 (d.f0 13146 165) (d.f1 13146 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13146 : ℝ) ^ 8 * (mA 13146 : ℝ) ^ 8 *
        ((((4203825837 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4203825837 / 1000000000000000000)) * ((350616813 / 250000000000000000)) * (126 / 100) +
          2 * (((350616813 / 250000000000000000)) ^ 2 + 2 * ((4203825837 / 1000000000000000000)) * ((674167 / 2000000000000000))) +
          6 * ((350616813 / 250000000000000000)) * ((674167 / 2000000000000000)) * (126 / 100) + 8 * ((674167 / 2000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13146) *
          (32 * (((4203825837 / 1000000000000000000) : ℝ) + (350616813 / 250000000000000000) + (674167 / 2000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13146 : ℝ) ^ 16 *
      (d.w0 13146 165 + d.w1 13146 165 * √(π / 2) + 2 * d.w2 13146 165 +
        energyR16 13146 * radiusPolynomialRoot16 (d.w0 13146 165) (d.w1 13146 165)
          (d.w2 13146 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13146 : ℝ) ^ 16 *
        (((330573223 / 20000000000000000000) : ℝ) + ((235196519 / 20000000000000000000)) * (126 / 100) + 2 * ((85934747 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13146) *
          (32 * (((330573223 / 20000000000000000000) : ℝ) + (235196519 / 20000000000000000000) + (85934747 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13146

/-! A coarse bound on the actual paper statistics constant at dimension 13147. -/
namespace BstLean.Part266.Row13147
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13145 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13145 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13145 128 ≤ (13399 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13399 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13147) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13147 : ℕ))
    (by norm_num : (13147 : ℕ) ≤ 16384)
  have ht : paperTail256 13147 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13147 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13147 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13147 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13147 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13147 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13145 128 * √(2 / (13147 : ℝ)) *
      (√(13147 : ℝ) + paperT0 13147 + paperTail256 13147) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13147 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13147 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13147 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13145 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13145 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13147 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13147

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13147
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13147 (61 / 100) 165 (17 / (100 * 13147)) (26 / (10 * 13147)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13147 (61 / 100) 165 (17 / (100 * 13147)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (429571937 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (261396177 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (387364373 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13147 / 13147 * (61 / 100)) ^ 4 * inverseRadius8 (13147 - 1) /
            envelopeGap 13147 (61 / 100) 165 (17 / (100 * 13147)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13147

namespace BstLean.Part266.Row13147
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13147 165 ≤ (2101511929 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13147 165 ≤ (1402199963 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (337019329 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13147 165 ≤ (1652488437 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13147 165 ≤ (235142801 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 13147 165 ≤ (42957569 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (429571937 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (429571937 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (261396177 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (387364373 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3595929 / 1000000000) : ℝ) ≤ √(17 / (100 * 13147) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13147) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2072611727 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18076095299 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13147) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13147) ≤ (107569299 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13147) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13147 * (165 : ℝ) ^ 2 + 26 / (10 * 13147) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13147) : ℝ)) (tA 13147 * 165 ^ 2 + 26 / (10 * 13147)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3595929 / 1000000000))) * ((429571937 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3595929 / 1000000000)) ^ 3) * ((261396177 / 200000000000000000000000))) + ((387364373 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3595929 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13147) : ℝ)) d.D d.V d.P (√(tA 13147) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3595929 / 1000000000)) ^ 2 * (((2072611727 / 1000000000000000)) * ((18076095299 / 500000000000000000)))) + ((387364373 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13147) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3595929 / 1000000000)) * ((429571937 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13147) : ℝ)) (tA 13147 * 165 ^ 2 + 26 / (10 * 13147)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((429571937 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3595929 / 1000000000)) ^ 2) * ((261396177 / 200000000000000000000000)) + ((387364373 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13147) : ℝ)) (√(26 / (10 * 13147) : ℝ)) d.D d.V d.P (√(tA 13147) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3595929 / 1000000000)) * (((2072611727 / 1000000000000000)) * ((18076095299 / 500000000000000000))) + ((387364373 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13147) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((429571937 / 100000000000000000000) : ℝ) + ((387364373 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13147

namespace BstLean.Part266.Row13147
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13147 165 ∧
    0 ≤ (tableEnvelope C).f1 13147 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13147 165 ∧
    0 ≤ (tableEnvelope C).w1 13147 165 ∧ 0 ≤ (tableEnvelope C).w2 13147 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13147 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13147 165 ∧ 0 ≤ d.f1 13147 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13147 165 ∧ 0 ≤ d.w1 13147 165 ∧ 0 ≤ d.w2 13147 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13147 ≤ 2 * (228 / 100 : ℝ) / 13147 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13147 ≤ 2 * (370 / 100 : ℝ) / 13147 := by
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
    (completeRAData (tableEnvelope C) 13147 165).locationBound 13147 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13147 165).energyBound 13147 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13147 165) (d.f1 13147 165) d.f2 ≤
      32 * (((2101511929 / 500000000000000000) : ℝ) + (1402199963 / 1000000000000000000) + (337019329 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13147 165) (d.w1 13147 165)
      (d.w2 13147 165) ≤
      32 * (((1652488437 / 100000000000000000000) : ℝ) + (235142801 / 20000000000000000000) + (42957569 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13147 165) (d.f1 13147 165) d.f2 ≤
      ((2101511929 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2101511929 / 500000000000000000)) * ((1402199963 / 1000000000000000000)) * (126 / 100) +
      2 * (((1402199963 / 1000000000000000000)) ^ 2 + 2 * ((2101511929 / 500000000000000000)) * ((337019329 / 1000000000000000000))) +
      6 * ((1402199963 / 1000000000000000000)) * ((337019329 / 1000000000000000000)) * (126 / 100) + 8 * ((337019329 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13147 165) (d.f1 13147 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13147 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13147 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13147 165) (d.f1 13147 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13147 165) (d.w1 13147 165) (d.w2 13147 165)
  have hwexpr0 : 0 ≤ d.w0 13147 165 + d.w1 13147 165 * √(π / 2) +
      2 * d.w2 13147 165 + energyR16 13147 *
      radiusPolynomialRoot16 (d.w0 13147 165) (d.w1 13147 165) (d.w2 13147 165) := by
    positivity
  constructor
  · change (13147 : ℝ) ^ 8 * (mA 13147 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13147 165) (d.f1 13147 165) d.f2 + locationR16 13147 *
        radiusPolynomialRoot16 (d.f0 13147 165) (d.f1 13147 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13147 : ℝ) ^ 8 * (mA 13147 : ℝ) ^ 8 *
        ((((2101511929 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2101511929 / 500000000000000000)) * ((1402199963 / 1000000000000000000)) * (126 / 100) +
          2 * (((1402199963 / 1000000000000000000)) ^ 2 + 2 * ((2101511929 / 500000000000000000)) * ((337019329 / 1000000000000000000))) +
          6 * ((1402199963 / 1000000000000000000)) * ((337019329 / 1000000000000000000)) * (126 / 100) + 8 * ((337019329 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13147) *
          (32 * (((2101511929 / 500000000000000000) : ℝ) + (1402199963 / 1000000000000000000) + (337019329 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13147 : ℝ) ^ 16 *
      (d.w0 13147 165 + d.w1 13147 165 * √(π / 2) + 2 * d.w2 13147 165 +
        energyR16 13147 * radiusPolynomialRoot16 (d.w0 13147 165) (d.w1 13147 165)
          (d.w2 13147 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13147 : ℝ) ^ 16 *
        (((1652488437 / 100000000000000000000) : ℝ) + ((235142801 / 20000000000000000000)) * (126 / 100) + 2 * ((42957569 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13147) *
          (32 * (((1652488437 / 100000000000000000000) : ℝ) + (235142801 / 20000000000000000000) + (42957569 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13147

/-! A coarse bound on the actual paper statistics constant at dimension 13148. -/
namespace BstLean.Part266.Row13148
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13146 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13146 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13146 128 ≤ (13400 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13400 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13148) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13148 : ℕ))
    (by norm_num : (13148 : ℕ) ≤ 16384)
  have ht : paperTail256 13148 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13148 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13148 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13148 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13148 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13148 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13146 128 * √(2 / (13148 : ℝ)) *
      (√(13148 : ℝ) + paperT0 13148 + paperTail256 13148) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13148 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13148 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13148 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13146 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13146 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13148 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13148

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13148
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13148 (61 / 100) 165 (17 / (100 * 13148)) (26 / (10 * 13148)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13148 (61 / 100) 165 (17 / (100 * 13148)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (429473923 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (653291647 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (387126547 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13148 / 13148 * (61 / 100)) ^ 4 * inverseRadius8 (13148 - 1) /
            envelopeGap 13148 (61 / 100) 165 (17 / (100 * 13148)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13148

namespace BstLean.Part266.Row13148
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13148 165 ≤ (52527819 / 12500000000000000)
  f1 : (tableEnvelope C).f1 13148 165 ≤ (700966769 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (33695527 / 100000000000000000)
  w0 : (tableEnvelope C).w0 13148 165 ≤ (413027891 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 13148 165 ≤ (293861457 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 13148 165 ≤ (214738837 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (429473923 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (429473923 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (653291647 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (387126547 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((224737 / 62500000) : ℝ) ≤ √(17 / (100 * 13148) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13148) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2072375263 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36146691329 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13148) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13148) ≤ (107561117 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13148) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13148 * (165 : ℝ) ^ 2 + 26 / (10 * 13148) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13148) : ℝ)) (tA 13148 * 165 ^ 2 + 26 / (10 * 13148)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((224737 / 62500000))) * ((429473923 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((224737 / 62500000)) ^ 3) * ((653291647 / 500000000000000000000000))) + ((387126547 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((224737 / 62500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13148) : ℝ)) d.D d.V d.P (√(tA 13148) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((224737 / 62500000)) ^ 2 * (((2072375263 / 1000000000000000)) * ((36146691329 / 1000000000000000000)))) + ((387126547 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13148) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((224737 / 62500000)) * ((429473923 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13148) : ℝ)) (tA 13148 * 165 ^ 2 + 26 / (10 * 13148)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((429473923 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((224737 / 62500000)) ^ 2) * ((653291647 / 500000000000000000000000)) + ((387126547 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13148) : ℝ)) (√(26 / (10 * 13148) : ℝ)) d.D d.V d.P (√(tA 13148) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((224737 / 62500000)) * (((2072375263 / 1000000000000000)) * ((36146691329 / 1000000000000000000))) + ((387126547 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13148) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((429473923 / 100000000000000000000) : ℝ) + ((387126547 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13148

namespace BstLean.Part266.Row13148
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13148 165 ∧
    0 ≤ (tableEnvelope C).f1 13148 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13148 165 ∧
    0 ≤ (tableEnvelope C).w1 13148 165 ∧ 0 ≤ (tableEnvelope C).w2 13148 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13148 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13148 165 ∧ 0 ≤ d.f1 13148 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13148 165 ∧ 0 ≤ d.w1 13148 165 ∧ 0 ≤ d.w2 13148 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13148 ≤ 2 * (228 / 100 : ℝ) / 13148 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13148 ≤ 2 * (370 / 100 : ℝ) / 13148 := by
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
    (completeRAData (tableEnvelope C) 13148 165).locationBound 13148 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13148 165).energyBound 13148 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13148 165) (d.f1 13148 165) d.f2 ≤
      32 * (((52527819 / 12500000000000000) : ℝ) + (700966769 / 500000000000000000) + (33695527 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13148 165) (d.w1 13148 165)
      (d.w2 13148 165) ≤
      32 * (((413027891 / 25000000000000000000) : ℝ) + (293861457 / 25000000000000000000) + (214738837 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13148 165) (d.f1 13148 165) d.f2 ≤
      ((52527819 / 12500000000000000) : ℝ) ^ 2 + 2 * ((52527819 / 12500000000000000)) * ((700966769 / 500000000000000000)) * (126 / 100) +
      2 * (((700966769 / 500000000000000000)) ^ 2 + 2 * ((52527819 / 12500000000000000)) * ((33695527 / 100000000000000000))) +
      6 * ((700966769 / 500000000000000000)) * ((33695527 / 100000000000000000)) * (126 / 100) + 8 * ((33695527 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13148 165) (d.f1 13148 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13148 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13148 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13148 165) (d.f1 13148 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13148 165) (d.w1 13148 165) (d.w2 13148 165)
  have hwexpr0 : 0 ≤ d.w0 13148 165 + d.w1 13148 165 * √(π / 2) +
      2 * d.w2 13148 165 + energyR16 13148 *
      radiusPolynomialRoot16 (d.w0 13148 165) (d.w1 13148 165) (d.w2 13148 165) := by
    positivity
  constructor
  · change (13148 : ℝ) ^ 8 * (mA 13148 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13148 165) (d.f1 13148 165) d.f2 + locationR16 13148 *
        radiusPolynomialRoot16 (d.f0 13148 165) (d.f1 13148 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13148 : ℝ) ^ 8 * (mA 13148 : ℝ) ^ 8 *
        ((((52527819 / 12500000000000000) : ℝ) ^ 2 + 2 * ((52527819 / 12500000000000000)) * ((700966769 / 500000000000000000)) * (126 / 100) +
          2 * (((700966769 / 500000000000000000)) ^ 2 + 2 * ((52527819 / 12500000000000000)) * ((33695527 / 100000000000000000))) +
          6 * ((700966769 / 500000000000000000)) * ((33695527 / 100000000000000000)) * (126 / 100) + 8 * ((33695527 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13148) *
          (32 * (((52527819 / 12500000000000000) : ℝ) + (700966769 / 500000000000000000) + (33695527 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13148 : ℝ) ^ 16 *
      (d.w0 13148 165 + d.w1 13148 165 * √(π / 2) + 2 * d.w2 13148 165 +
        energyR16 13148 * radiusPolynomialRoot16 (d.w0 13148 165) (d.w1 13148 165)
          (d.w2 13148 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13148 : ℝ) ^ 16 *
        (((413027891 / 25000000000000000000) : ℝ) + ((293861457 / 25000000000000000000)) * (126 / 100) + 2 * ((214738837 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13148) *
          (32 * (((413027891 / 25000000000000000000) : ℝ) + (293861457 / 25000000000000000000) + (214738837 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13148

/-! A coarse bound on the actual paper statistics constant at dimension 13149. -/
namespace BstLean.Part266.Row13149
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13147 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13147 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13147 128 ≤ (13401 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13401 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13149) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13149 : ℕ))
    (by norm_num : (13149 : ℕ) ≤ 16384)
  have ht : paperTail256 13149 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13149 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13149 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13149 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13149 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13149 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13147 128 * √(2 / (13149 : ℝ)) *
      (√(13149 : ℝ) + paperT0 13149 + paperTail256 13149) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13149 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13149 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13149 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13147 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13147 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13149 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13149

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13149
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13149 (61 / 100) 165 (17 / (100 * 13149)) (26 / (10 * 13149)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13149 (61 / 100) 165 (17 / (100 * 13149)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (429375939 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (261237171 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1934444427 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13149 / 13149 * (61 / 100)) ^ 4 * inverseRadius8 (13149 - 1) /
            envelopeGap 13149 (61 / 100) 165 (17 / (100 * 13149)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13149

namespace BstLean.Part266.Row13149
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13149 165 ≤ (4201427449 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13149 165 ≤ (350416799 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (33689123 / 100000000000000000)
  w0 : (tableEnvelope C).w0 13149 165 ≤ (825867409 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13149 165 ≤ (1175177739 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13149 165 ≤ (429379687 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (429375939 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (429375939 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (261237171 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1934444427 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((719131 / 200000000) : ℝ) ≤ √(17 / (100 * 13149) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13149) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (414427769 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18070596663 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13149) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13149) ≤ (107552937 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13149) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13149 * (165 : ℝ) ^ 2 + 26 / (10 * 13149) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13149) : ℝ)) (tA 13149 * 165 ^ 2 + 26 / (10 * 13149)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((719131 / 200000000))) * ((429375939 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((719131 / 200000000)) ^ 3) * ((261237171 / 200000000000000000000000))) + ((1934444427 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((719131 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13149) : ℝ)) d.D d.V d.P (√(tA 13149) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((719131 / 200000000)) ^ 2 * (((414427769 / 200000000000000)) * ((18070596663 / 500000000000000000)))) + ((1934444427 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13149) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((719131 / 200000000)) * ((429375939 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13149) : ℝ)) (tA 13149 * 165 ^ 2 + 26 / (10 * 13149)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((429375939 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((719131 / 200000000)) ^ 2) * ((261237171 / 200000000000000000000000)) + ((1934444427 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13149) : ℝ)) (√(26 / (10 * 13149) : ℝ)) d.D d.V d.P (√(tA 13149) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((719131 / 200000000)) * (((414427769 / 200000000000000)) * ((18070596663 / 500000000000000000))) + ((1934444427 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13149) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((429375939 / 100000000000000000000) : ℝ) + ((1934444427 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13149

namespace BstLean.Part266.Row13149
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13149 165 ∧
    0 ≤ (tableEnvelope C).f1 13149 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13149 165 ∧
    0 ≤ (tableEnvelope C).w1 13149 165 ∧ 0 ≤ (tableEnvelope C).w2 13149 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13149 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13149 165 ∧ 0 ≤ d.f1 13149 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13149 165 ∧ 0 ≤ d.w1 13149 165 ∧ 0 ≤ d.w2 13149 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13149 ≤ 2 * (228 / 100 : ℝ) / 13149 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13149 ≤ 2 * (370 / 100 : ℝ) / 13149 := by
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
    (completeRAData (tableEnvelope C) 13149 165).locationBound 13149 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13149 165).energyBound 13149 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13149 165) (d.f1 13149 165) d.f2 ≤
      32 * (((4201427449 / 1000000000000000000) : ℝ) + (350416799 / 250000000000000000) + (33689123 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13149 165) (d.w1 13149 165)
      (d.w2 13149 165) ≤
      32 * (((825867409 / 50000000000000000000) : ℝ) + (1175177739 / 100000000000000000000) + (429379687 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13149 165) (d.f1 13149 165) d.f2 ≤
      ((4201427449 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4201427449 / 1000000000000000000)) * ((350416799 / 250000000000000000)) * (126 / 100) +
      2 * (((350416799 / 250000000000000000)) ^ 2 + 2 * ((4201427449 / 1000000000000000000)) * ((33689123 / 100000000000000000))) +
      6 * ((350416799 / 250000000000000000)) * ((33689123 / 100000000000000000)) * (126 / 100) + 8 * ((33689123 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13149 165) (d.f1 13149 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13149 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13149 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13149 165) (d.f1 13149 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13149 165) (d.w1 13149 165) (d.w2 13149 165)
  have hwexpr0 : 0 ≤ d.w0 13149 165 + d.w1 13149 165 * √(π / 2) +
      2 * d.w2 13149 165 + energyR16 13149 *
      radiusPolynomialRoot16 (d.w0 13149 165) (d.w1 13149 165) (d.w2 13149 165) := by
    positivity
  constructor
  · change (13149 : ℝ) ^ 8 * (mA 13149 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13149 165) (d.f1 13149 165) d.f2 + locationR16 13149 *
        radiusPolynomialRoot16 (d.f0 13149 165) (d.f1 13149 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13149 : ℝ) ^ 8 * (mA 13149 : ℝ) ^ 8 *
        ((((4201427449 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4201427449 / 1000000000000000000)) * ((350416799 / 250000000000000000)) * (126 / 100) +
          2 * (((350416799 / 250000000000000000)) ^ 2 + 2 * ((4201427449 / 1000000000000000000)) * ((33689123 / 100000000000000000))) +
          6 * ((350416799 / 250000000000000000)) * ((33689123 / 100000000000000000)) * (126 / 100) + 8 * ((33689123 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13149) *
          (32 * (((4201427449 / 1000000000000000000) : ℝ) + (350416799 / 250000000000000000) + (33689123 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13149 : ℝ) ^ 16 *
      (d.w0 13149 165 + d.w1 13149 165 * √(π / 2) + 2 * d.w2 13149 165 +
        energyR16 13149 * radiusPolynomialRoot16 (d.w0 13149 165) (d.w1 13149 165)
          (d.w2 13149 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13149 : ℝ) ^ 16 *
        (((825867409 / 50000000000000000000) : ℝ) + ((1175177739 / 100000000000000000000)) * (126 / 100) + 2 * ((429379687 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13149) *
          (32 * (((825867409 / 50000000000000000000) : ℝ) + (1175177739 / 100000000000000000000) + (429379687 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13149
