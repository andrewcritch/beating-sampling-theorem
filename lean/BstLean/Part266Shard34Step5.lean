import BstLean.Part266Shard34Step4


/-! A coarse bound on the actual paper statistics constant at dimension 13200. -/
namespace BstLean.Part266.Row13200
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13198 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13198 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13198 128 ≤ (13452 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13452 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13200) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13200 : ℕ))
    (by norm_num : (13200 : ℕ) ≤ 16384)
  have ht : paperTail256 13200 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13200 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13200 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13200 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13200 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13200 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13198 128 * √(2 / (13200 : ℝ)) *
      (√(13200 : ℝ) + paperT0 13200 + paperTail256 13200) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13200 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13200 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13200 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13198 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13198 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13200 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13200

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13200
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13200 (61 / 100) 166 (17 / (100 * 13200)) (26 / (10 * 13200)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13200 (61 / 100) 166 (17 / (100 * 13200)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (106104509 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1286115279 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3751476227 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13200 / 13200 * (61 / 100)) ^ 4 * inverseRadius8 (13200 - 1) /
            envelopeGap 13200 (61 / 100) 166 (17 / (100 * 13200)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13200

namespace BstLean.Part266.Row13200
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13200 166 ≤ (4160960967 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13200 166 ≤ (347041711 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (66729281 / 200000000000000000)
  w0 : (tableEnvelope C).w0 13200 166 ≤ (1632662693 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13200 166 ≤ (290402067 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 13200 166 ≤ (424421671 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (106104509 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (106104509 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1286115279 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3751476227 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1794351 / 500000000) : ℝ) ≤ √(17 / (100 * 13200) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13200) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (103007043 / 50000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (35862449429 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13200) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13200) ≤ (6696087 / 62500000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13200) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13200 * (166 : ℝ) ^ 2 + 26 / (10 * 13200) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13200) : ℝ)) (tA 13200 * 166 ^ 2 + 26 / (10 * 13200)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1794351 / 500000000))) * ((106104509 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1794351 / 500000000)) ^ 3) * ((1286115279 / 1000000000000000000000000))) + ((3751476227 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1794351 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13200) : ℝ)) d.D d.V d.P (√(tA 13200) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1794351 / 500000000)) ^ 2 * (((103007043 / 50000000000000)) * ((35862449429 / 1000000000000000000)))) + ((3751476227 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13200) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1794351 / 500000000)) * ((106104509 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13200) : ℝ)) (tA 13200 * 166 ^ 2 + 26 / (10 * 13200)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((106104509 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1794351 / 500000000)) ^ 2) * ((1286115279 / 1000000000000000000000000)) + ((3751476227 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13200) : ℝ)) (√(26 / (10 * 13200) : ℝ)) d.D d.V d.P (√(tA 13200) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1794351 / 500000000)) * (((103007043 / 50000000000000)) * ((35862449429 / 1000000000000000000))) + ((3751476227 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13200) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((106104509 / 25000000000000000000) : ℝ) + ((3751476227 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13200

namespace BstLean.Part266.Row13200
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13200 166 ∧
    0 ≤ (tableEnvelope C).f1 13200 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13200 166 ∧
    0 ≤ (tableEnvelope C).w1 13200 166 ∧ 0 ≤ (tableEnvelope C).w2 13200 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13200 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13200 166 ∧ 0 ≤ d.f1 13200 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13200 166 ∧ 0 ≤ d.w1 13200 166 ∧ 0 ≤ d.w2 13200 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13200 ≤ 2 * (228 / 100 : ℝ) / 13200 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13200 ≤ 2 * (370 / 100 : ℝ) / 13200 := by
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
    (completeRAData (tableEnvelope C) 13200 166).locationBound 13200 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13200 166).energyBound 13200 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13200 166) (d.f1 13200 166) d.f2 ≤
      32 * (((4160960967 / 1000000000000000000) : ℝ) + (347041711 / 250000000000000000) + (66729281 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13200 166) (d.w1 13200 166)
      (d.w2 13200 166) ≤
      32 * (((1632662693 / 100000000000000000000) : ℝ) + (290402067 / 25000000000000000000) + (424421671 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13200 166) (d.f1 13200 166) d.f2 ≤
      ((4160960967 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4160960967 / 1000000000000000000)) * ((347041711 / 250000000000000000)) * (126 / 100) +
      2 * (((347041711 / 250000000000000000)) ^ 2 + 2 * ((4160960967 / 1000000000000000000)) * ((66729281 / 200000000000000000))) +
      6 * ((347041711 / 250000000000000000)) * ((66729281 / 200000000000000000)) * (126 / 100) + 8 * ((66729281 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13200 166) (d.f1 13200 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13200 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13200 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13200 166) (d.f1 13200 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13200 166) (d.w1 13200 166) (d.w2 13200 166)
  have hwexpr0 : 0 ≤ d.w0 13200 166 + d.w1 13200 166 * √(π / 2) +
      2 * d.w2 13200 166 + energyR16 13200 *
      radiusPolynomialRoot16 (d.w0 13200 166) (d.w1 13200 166) (d.w2 13200 166) := by
    positivity
  constructor
  · change (13200 : ℝ) ^ 8 * (mA 13200 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13200 166) (d.f1 13200 166) d.f2 + locationR16 13200 *
        radiusPolynomialRoot16 (d.f0 13200 166) (d.f1 13200 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13200 : ℝ) ^ 8 * (mA 13200 : ℝ) ^ 8 *
        ((((4160960967 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4160960967 / 1000000000000000000)) * ((347041711 / 250000000000000000)) * (126 / 100) +
          2 * (((347041711 / 250000000000000000)) ^ 2 + 2 * ((4160960967 / 1000000000000000000)) * ((66729281 / 200000000000000000))) +
          6 * ((347041711 / 250000000000000000)) * ((66729281 / 200000000000000000)) * (126 / 100) + 8 * ((66729281 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13200) *
          (32 * (((4160960967 / 1000000000000000000) : ℝ) + (347041711 / 250000000000000000) + (66729281 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13200 : ℝ) ^ 16 *
      (d.w0 13200 166 + d.w1 13200 166 * √(π / 2) + 2 * d.w2 13200 166 +
        energyR16 13200 * radiusPolynomialRoot16 (d.w0 13200 166) (d.w1 13200 166)
          (d.w2 13200 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13200 : ℝ) ^ 16 *
        (((1632662693 / 100000000000000000000) : ℝ) + ((290402067 / 25000000000000000000)) * (126 / 100) + 2 * ((424421671 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13200) *
          (32 * (((1632662693 / 100000000000000000000) : ℝ) + (290402067 / 25000000000000000000) + (424421671 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13200

/-! A coarse bound on the actual paper statistics constant at dimension 13201. -/
namespace BstLean.Part266.Row13201
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13199 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13199 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13199 128 ≤ (13453 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13453 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13201) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13201 : ℕ))
    (by norm_num : (13201 : ℕ) ≤ 16384)
  have ht : paperTail256 13201 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13201 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13201 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13201 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13201 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13201 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13199 128 * √(2 / (13201 : ℝ)) *
      (√(13201 : ℝ) + paperT0 13201 + paperTail256 13201) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13201 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13201 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13201 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13199 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13199 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13201 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13201

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13201
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13201 (61 / 100) 166 (17 / (100 * 13201)) (26 / (10 * 13201)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13201 (61 / 100) 166 (17 / (100 * 13201)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (424321587 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (642862803 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (749836427 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13201 / 13201 * (61 / 100)) ^ 4 * inverseRadius8 (13201 - 1) /
            envelopeGap 13201 (61 / 100) 166 (17 / (100 * 13201)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13201

namespace BstLean.Part266.Row13201
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13201 166 ≤ (1040043301 / 250000000000000000)
  f1 : (tableEnvelope C).f1 13201 166 ≤ (173488001 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (166791613 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13201 166 ≤ (816145859 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13201 166 ≤ (232268863 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 13201 166 ≤ (424325219 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (424321587 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (424321587 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (642862803 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (749836427 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1794283 / 500000000) : ℝ) ≤ √(17 / (100 * 13201) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13201) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2059906763 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (17928508067 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13201) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13201) ≤ (26782319 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13201) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13201 * (166 : ℝ) ^ 2 + 26 / (10 * 13201) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13201) : ℝ)) (tA 13201 * 166 ^ 2 + 26 / (10 * 13201)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1794283 / 500000000))) * ((424321587 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1794283 / 500000000)) ^ 3) * ((642862803 / 500000000000000000000000))) + ((749836427 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1794283 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13201) : ℝ)) d.D d.V d.P (√(tA 13201) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1794283 / 500000000)) ^ 2 * (((2059906763 / 1000000000000000)) * ((17928508067 / 500000000000000000)))) + ((749836427 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13201) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1794283 / 500000000)) * ((424321587 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13201) : ℝ)) (tA 13201 * 166 ^ 2 + 26 / (10 * 13201)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((424321587 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1794283 / 500000000)) ^ 2) * ((642862803 / 500000000000000000000000)) + ((749836427 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13201) : ℝ)) (√(26 / (10 * 13201) : ℝ)) d.D d.V d.P (√(tA 13201) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1794283 / 500000000)) * (((2059906763 / 1000000000000000)) * ((17928508067 / 500000000000000000))) + ((749836427 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13201) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((424321587 / 100000000000000000000) : ℝ) + ((749836427 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13201

namespace BstLean.Part266.Row13201
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13201 166 ∧
    0 ≤ (tableEnvelope C).f1 13201 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13201 166 ∧
    0 ≤ (tableEnvelope C).w1 13201 166 ∧ 0 ≤ (tableEnvelope C).w2 13201 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13201 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13201 166 ∧ 0 ≤ d.f1 13201 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13201 166 ∧ 0 ≤ d.w1 13201 166 ∧ 0 ≤ d.w2 13201 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13201 ≤ 2 * (228 / 100 : ℝ) / 13201 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13201 ≤ 2 * (370 / 100 : ℝ) / 13201 := by
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
    (completeRAData (tableEnvelope C) 13201 166).locationBound 13201 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13201 166).energyBound 13201 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13201 166) (d.f1 13201 166) d.f2 ≤
      32 * (((1040043301 / 250000000000000000) : ℝ) + (173488001 / 125000000000000000) + (166791613 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13201 166) (d.w1 13201 166)
      (d.w2 13201 166) ≤
      32 * (((816145859 / 50000000000000000000) : ℝ) + (232268863 / 20000000000000000000) + (424325219 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13201 166) (d.f1 13201 166) d.f2 ≤
      ((1040043301 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1040043301 / 250000000000000000)) * ((173488001 / 125000000000000000)) * (126 / 100) +
      2 * (((173488001 / 125000000000000000)) ^ 2 + 2 * ((1040043301 / 250000000000000000)) * ((166791613 / 500000000000000000))) +
      6 * ((173488001 / 125000000000000000)) * ((166791613 / 500000000000000000)) * (126 / 100) + 8 * ((166791613 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13201 166) (d.f1 13201 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13201 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13201 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13201 166) (d.f1 13201 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13201 166) (d.w1 13201 166) (d.w2 13201 166)
  have hwexpr0 : 0 ≤ d.w0 13201 166 + d.w1 13201 166 * √(π / 2) +
      2 * d.w2 13201 166 + energyR16 13201 *
      radiusPolynomialRoot16 (d.w0 13201 166) (d.w1 13201 166) (d.w2 13201 166) := by
    positivity
  constructor
  · change (13201 : ℝ) ^ 8 * (mA 13201 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13201 166) (d.f1 13201 166) d.f2 + locationR16 13201 *
        radiusPolynomialRoot16 (d.f0 13201 166) (d.f1 13201 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13201 : ℝ) ^ 8 * (mA 13201 : ℝ) ^ 8 *
        ((((1040043301 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1040043301 / 250000000000000000)) * ((173488001 / 125000000000000000)) * (126 / 100) +
          2 * (((173488001 / 125000000000000000)) ^ 2 + 2 * ((1040043301 / 250000000000000000)) * ((166791613 / 500000000000000000))) +
          6 * ((173488001 / 125000000000000000)) * ((166791613 / 500000000000000000)) * (126 / 100) + 8 * ((166791613 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13201) *
          (32 * (((1040043301 / 250000000000000000) : ℝ) + (173488001 / 125000000000000000) + (166791613 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13201 : ℝ) ^ 16 *
      (d.w0 13201 166 + d.w1 13201 166 * √(π / 2) + 2 * d.w2 13201 166 +
        energyR16 13201 * radiusPolynomialRoot16 (d.w0 13201 166) (d.w1 13201 166)
          (d.w2 13201 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13201 : ℝ) ^ 16 *
        (((816145859 / 50000000000000000000) : ℝ) + ((232268863 / 20000000000000000000)) * (126 / 100) + 2 * ((424325219 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13201) *
          (32 * (((816145859 / 50000000000000000000) : ℝ) + (232268863 / 20000000000000000000) + (424325219 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13201

/-! A coarse bound on the actual paper statistics constant at dimension 13202. -/
namespace BstLean.Part266.Row13202
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13200 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13200 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13200 128 ≤ (13454 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13454 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13202) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13202 : ℕ))
    (by norm_num : (13202 : ℕ) ≤ 16384)
  have ht : paperTail256 13202 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13202 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13202 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13202 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13202 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13202 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13200 128 * √(2 / (13202 : ℝ)) *
      (√(13202 : ℝ) + paperT0 13202 + paperTail256 13202) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13202 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13202 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13202 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13200 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13200 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13202 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13202

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13202
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13202 (61 / 100) 166 (17 / (100 * 13202)) (26 / (10 * 13202)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13202 (61 / 100) 166 (17 / (100 * 13202)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (26514073 / 6250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1285336081 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (468361203 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13202 / 13202 * (61 / 100)) ^ 4 * inverseRadius8 (13202 - 1) /
            envelopeGap 13202 (61 / 100) 166 (17 / (100 * 13202)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13202

namespace BstLean.Part266.Row13202
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13202 166 ≤ (2079692851 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13202 166 ≤ (277528251 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (66704013 / 200000000000000000)
  w0 : (tableEnvelope C).w0 13202 166 ≤ (407980217 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 13202 166 ≤ (1161080449 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13202 166 ≤ (212114399 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (26514073 / 6250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (26514073 / 6250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1285336081 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (468361203 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((358843 / 100000000) : ℝ) ≤ √(17 / (100 * 13202) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13202) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (257459089 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (448144801 / 12500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13202) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13202) ≤ (107121161 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13202) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13202 * (166 : ℝ) ^ 2 + 26 / (10 * 13202) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13202) : ℝ)) (tA 13202 * 166 ^ 2 + 26 / (10 * 13202)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((358843 / 100000000))) * ((26514073 / 6250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((358843 / 100000000)) ^ 3) * ((1285336081 / 1000000000000000000000000))) + ((468361203 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((358843 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13202) : ℝ)) d.D d.V d.P (√(tA 13202) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((358843 / 100000000)) ^ 2 * (((257459089 / 125000000000000)) * ((448144801 / 12500000000000000)))) + ((468361203 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13202) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((358843 / 100000000)) * ((26514073 / 6250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13202) : ℝ)) (tA 13202 * 166 ^ 2 + 26 / (10 * 13202)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((26514073 / 6250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((358843 / 100000000)) ^ 2) * ((1285336081 / 1000000000000000000000000)) + ((468361203 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13202) : ℝ)) (√(26 / (10 * 13202) : ℝ)) d.D d.V d.P (√(tA 13202) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((358843 / 100000000)) * (((257459089 / 125000000000000)) * ((448144801 / 12500000000000000))) + ((468361203 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13202) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((26514073 / 6250000000000000000) : ℝ) + ((468361203 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13202

namespace BstLean.Part266.Row13202
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13202 166 ∧
    0 ≤ (tableEnvelope C).f1 13202 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13202 166 ∧
    0 ≤ (tableEnvelope C).w1 13202 166 ∧ 0 ≤ (tableEnvelope C).w2 13202 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13202 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13202 166 ∧ 0 ≤ d.f1 13202 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13202 166 ∧ 0 ≤ d.w1 13202 166 ∧ 0 ≤ d.w2 13202 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13202 ≤ 2 * (228 / 100 : ℝ) / 13202 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13202 ≤ 2 * (370 / 100 : ℝ) / 13202 := by
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
    (completeRAData (tableEnvelope C) 13202 166).locationBound 13202 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13202 166).energyBound 13202 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13202 166) (d.f1 13202 166) d.f2 ≤
      32 * (((2079692851 / 500000000000000000) : ℝ) + (277528251 / 200000000000000000) + (66704013 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13202 166) (d.w1 13202 166)
      (d.w2 13202 166) ≤
      32 * (((407980217 / 25000000000000000000) : ℝ) + (1161080449 / 100000000000000000000) + (212114399 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13202 166) (d.f1 13202 166) d.f2 ≤
      ((2079692851 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2079692851 / 500000000000000000)) * ((277528251 / 200000000000000000)) * (126 / 100) +
      2 * (((277528251 / 200000000000000000)) ^ 2 + 2 * ((2079692851 / 500000000000000000)) * ((66704013 / 200000000000000000))) +
      6 * ((277528251 / 200000000000000000)) * ((66704013 / 200000000000000000)) * (126 / 100) + 8 * ((66704013 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13202 166) (d.f1 13202 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13202 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13202 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13202 166) (d.f1 13202 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13202 166) (d.w1 13202 166) (d.w2 13202 166)
  have hwexpr0 : 0 ≤ d.w0 13202 166 + d.w1 13202 166 * √(π / 2) +
      2 * d.w2 13202 166 + energyR16 13202 *
      radiusPolynomialRoot16 (d.w0 13202 166) (d.w1 13202 166) (d.w2 13202 166) := by
    positivity
  constructor
  · change (13202 : ℝ) ^ 8 * (mA 13202 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13202 166) (d.f1 13202 166) d.f2 + locationR16 13202 *
        radiusPolynomialRoot16 (d.f0 13202 166) (d.f1 13202 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13202 : ℝ) ^ 8 * (mA 13202 : ℝ) ^ 8 *
        ((((2079692851 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2079692851 / 500000000000000000)) * ((277528251 / 200000000000000000)) * (126 / 100) +
          2 * (((277528251 / 200000000000000000)) ^ 2 + 2 * ((2079692851 / 500000000000000000)) * ((66704013 / 200000000000000000))) +
          6 * ((277528251 / 200000000000000000)) * ((66704013 / 200000000000000000)) * (126 / 100) + 8 * ((66704013 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13202) *
          (32 * (((2079692851 / 500000000000000000) : ℝ) + (277528251 / 200000000000000000) + (66704013 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13202 : ℝ) ^ 16 *
      (d.w0 13202 166 + d.w1 13202 166 * √(π / 2) + 2 * d.w2 13202 166 +
        energyR16 13202 * radiusPolynomialRoot16 (d.w0 13202 166) (d.w1 13202 166)
          (d.w2 13202 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13202 : ℝ) ^ 16 *
        (((407980217 / 25000000000000000000) : ℝ) + ((1161080449 / 100000000000000000000)) * (126 / 100) + 2 * ((212114399 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13202) *
          (32 * (((407980217 / 25000000000000000000) : ℝ) + (1161080449 / 100000000000000000000) + (212114399 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13202

/-! A coarse bound on the actual paper statistics constant at dimension 13203. -/
namespace BstLean.Part266.Row13203
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13201 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13201 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13201 128 ≤ (13455 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13455 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13203) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13203 : ℕ))
    (by norm_num : (13203 : ℕ) ≤ 16384)
  have ht : paperTail256 13203 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13203 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13203 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13203 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13203 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13203 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13201 128 * √(2 / (13203 : ℝ)) *
      (√(13203 : ℝ) + paperT0 13203 + paperTail256 13203) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13203 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13203 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13203 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13201 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13201 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13203 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13203

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13203
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13203 (61 / 100) 166 (17 / (100 * 13203)) (26 / (10 * 13203)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13203 (61 / 100) 166 (17 / (100 * 13203)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (424128777 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1284946703 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (374459869 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13203 / 13203 * (61 / 100)) ^ 4 * inverseRadius8 (13203 - 1) /
            envelopeGap 13203 (61 / 100) 166 (17 / (100 * 13203)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13203

namespace BstLean.Part266.Row13203
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13203 166 ≤ (2079297557 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13203 166 ≤ (86711113 / 62500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (333456829 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13203 166 ≤ (815774733 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13203 166 ≤ (580408171 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13203 166 ≤ (84826481 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (424128777 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (424128777 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1284946703 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (374459869 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((717659 / 200000000) : ℝ) ≤ √(17 / (100 * 13203) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13203) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2059438703 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (35846153253 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13203) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13203) ≤ (13389131 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13203) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13203 * (166 : ℝ) ^ 2 + 26 / (10 * 13203) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13203) : ℝ)) (tA 13203 * 166 ^ 2 + 26 / (10 * 13203)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((717659 / 200000000))) * ((424128777 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((717659 / 200000000)) ^ 3) * ((1284946703 / 1000000000000000000000000))) + ((374459869 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((717659 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13203) : ℝ)) d.D d.V d.P (√(tA 13203) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((717659 / 200000000)) ^ 2 * (((2059438703 / 1000000000000000)) * ((35846153253 / 1000000000000000000)))) + ((374459869 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13203) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((717659 / 200000000)) * ((424128777 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13203) : ℝ)) (tA 13203 * 166 ^ 2 + 26 / (10 * 13203)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((424128777 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((717659 / 200000000)) ^ 2) * ((1284946703 / 1000000000000000000000000)) + ((374459869 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13203) : ℝ)) (√(26 / (10 * 13203) : ℝ)) d.D d.V d.P (√(tA 13203) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((717659 / 200000000)) * (((2059438703 / 1000000000000000)) * ((35846153253 / 1000000000000000000))) + ((374459869 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13203) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((424128777 / 100000000000000000000) : ℝ) + ((374459869 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13203

namespace BstLean.Part266.Row13203
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13203 166 ∧
    0 ≤ (tableEnvelope C).f1 13203 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13203 166 ∧
    0 ≤ (tableEnvelope C).w1 13203 166 ∧ 0 ≤ (tableEnvelope C).w2 13203 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13203 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13203 166 ∧ 0 ≤ d.f1 13203 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13203 166 ∧ 0 ≤ d.w1 13203 166 ∧ 0 ≤ d.w2 13203 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13203 ≤ 2 * (228 / 100 : ℝ) / 13203 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13203 ≤ 2 * (370 / 100 : ℝ) / 13203 := by
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
    (completeRAData (tableEnvelope C) 13203 166).locationBound 13203 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13203 166).energyBound 13203 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13203 166) (d.f1 13203 166) d.f2 ≤
      32 * (((2079297557 / 500000000000000000) : ℝ) + (86711113 / 62500000000000000) + (333456829 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13203 166) (d.w1 13203 166)
      (d.w2 13203 166) ≤
      32 * (((815774733 / 50000000000000000000) : ℝ) + (580408171 / 50000000000000000000) + (84826481 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13203 166) (d.f1 13203 166) d.f2 ≤
      ((2079297557 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2079297557 / 500000000000000000)) * ((86711113 / 62500000000000000)) * (126 / 100) +
      2 * (((86711113 / 62500000000000000)) ^ 2 + 2 * ((2079297557 / 500000000000000000)) * ((333456829 / 1000000000000000000))) +
      6 * ((86711113 / 62500000000000000)) * ((333456829 / 1000000000000000000)) * (126 / 100) + 8 * ((333456829 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13203 166) (d.f1 13203 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13203 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13203 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13203 166) (d.f1 13203 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13203 166) (d.w1 13203 166) (d.w2 13203 166)
  have hwexpr0 : 0 ≤ d.w0 13203 166 + d.w1 13203 166 * √(π / 2) +
      2 * d.w2 13203 166 + energyR16 13203 *
      radiusPolynomialRoot16 (d.w0 13203 166) (d.w1 13203 166) (d.w2 13203 166) := by
    positivity
  constructor
  · change (13203 : ℝ) ^ 8 * (mA 13203 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13203 166) (d.f1 13203 166) d.f2 + locationR16 13203 *
        radiusPolynomialRoot16 (d.f0 13203 166) (d.f1 13203 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13203 : ℝ) ^ 8 * (mA 13203 : ℝ) ^ 8 *
        ((((2079297557 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2079297557 / 500000000000000000)) * ((86711113 / 62500000000000000)) * (126 / 100) +
          2 * (((86711113 / 62500000000000000)) ^ 2 + 2 * ((2079297557 / 500000000000000000)) * ((333456829 / 1000000000000000000))) +
          6 * ((86711113 / 62500000000000000)) * ((333456829 / 1000000000000000000)) * (126 / 100) + 8 * ((333456829 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13203) *
          (32 * (((2079297557 / 500000000000000000) : ℝ) + (86711113 / 62500000000000000) + (333456829 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13203 : ℝ) ^ 16 *
      (d.w0 13203 166 + d.w1 13203 166 * √(π / 2) + 2 * d.w2 13203 166 +
        energyR16 13203 * radiusPolynomialRoot16 (d.w0 13203 166) (d.w1 13203 166)
          (d.w2 13203 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13203 : ℝ) ^ 16 *
        (((815774733 / 50000000000000000000) : ℝ) + ((580408171 / 50000000000000000000)) * (126 / 100) + 2 * ((84826481 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13203) *
          (32 * (((815774733 / 50000000000000000000) : ℝ) + (580408171 / 50000000000000000000) + (84826481 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13203

/-! A coarse bound on the actual paper statistics constant at dimension 13204. -/
namespace BstLean.Part266.Row13204
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13202 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13202 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13202 128 ≤ (13456 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13456 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13204) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13204 : ℕ))
    (by norm_num : (13204 : ℕ) ≤ 16384)
  have ht : paperTail256 13204 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13204 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13204 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13204 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13204 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13204 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13202 128 * √(2 / (13204 : ℝ)) *
      (√(13204 : ℝ) + paperT0 13204 + paperTail256 13204) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13204 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13204 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13204 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13202 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13202 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13204 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13204

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13204
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13204 (61 / 100) 166 (17 / (100 * 13204)) (26 / (10 * 13204)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13204 (61 / 100) 166 (17 / (100 * 13204)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (13251013 / 3125000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1284557473 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (748461867 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13204 / 13204 * (61 / 100)) ^ 4 * inverseRadius8 (13204 - 1) /
            envelopeGap 13204 (61 / 100) 166 (17 / (100 * 13204)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13204

namespace BstLean.Part266.Row13204
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13204 166 ≤ (4157808133 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13204 166 ≤ (1387115217 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (41674213 / 125000000000000000)
  w0 : (tableEnvelope C).w0 13204 166 ≤ (1631178861 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13204 166 ≤ (580276323 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13204 166 ≤ (212018021 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (13251013 / 3125000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (13251013 / 3125000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1284557473 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (748461867 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3588159 / 1000000000) : ℝ) ≤ √(17 / (100 * 13204) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13204) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (102960237 / 50000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (8960180917 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13204) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13204) ≤ (13388117 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13204) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13204 * (166 : ℝ) ^ 2 + 26 / (10 * 13204) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13204) : ℝ)) (tA 13204 * 166 ^ 2 + 26 / (10 * 13204)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3588159 / 1000000000))) * ((13251013 / 3125000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3588159 / 1000000000)) ^ 3) * ((1284557473 / 1000000000000000000000000))) + ((748461867 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3588159 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13204) : ℝ)) d.D d.V d.P (√(tA 13204) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3588159 / 1000000000)) ^ 2 * (((102960237 / 50000000000000)) * ((8960180917 / 250000000000000000)))) + ((748461867 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13204) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3588159 / 1000000000)) * ((13251013 / 3125000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13204) : ℝ)) (tA 13204 * 166 ^ 2 + 26 / (10 * 13204)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((13251013 / 3125000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3588159 / 1000000000)) ^ 2) * ((1284557473 / 1000000000000000000000000)) + ((748461867 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13204) : ℝ)) (√(26 / (10 * 13204) : ℝ)) d.D d.V d.P (√(tA 13204) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3588159 / 1000000000)) * (((102960237 / 50000000000000)) * ((8960180917 / 250000000000000000))) + ((748461867 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13204) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((13251013 / 3125000000000000000) : ℝ) + ((748461867 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13204

namespace BstLean.Part266.Row13204
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13204 166 ∧
    0 ≤ (tableEnvelope C).f1 13204 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13204 166 ∧
    0 ≤ (tableEnvelope C).w1 13204 166 ∧ 0 ≤ (tableEnvelope C).w2 13204 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13204 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13204 166 ∧ 0 ≤ d.f1 13204 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13204 166 ∧ 0 ≤ d.w1 13204 166 ∧ 0 ≤ d.w2 13204 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13204 ≤ 2 * (228 / 100 : ℝ) / 13204 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13204 ≤ 2 * (370 / 100 : ℝ) / 13204 := by
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
    (completeRAData (tableEnvelope C) 13204 166).locationBound 13204 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13204 166).energyBound 13204 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13204 166) (d.f1 13204 166) d.f2 ≤
      32 * (((4157808133 / 1000000000000000000) : ℝ) + (1387115217 / 1000000000000000000) + (41674213 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13204 166) (d.w1 13204 166)
      (d.w2 13204 166) ≤
      32 * (((1631178861 / 100000000000000000000) : ℝ) + (580276323 / 50000000000000000000) + (212018021 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13204 166) (d.f1 13204 166) d.f2 ≤
      ((4157808133 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4157808133 / 1000000000000000000)) * ((1387115217 / 1000000000000000000)) * (126 / 100) +
      2 * (((1387115217 / 1000000000000000000)) ^ 2 + 2 * ((4157808133 / 1000000000000000000)) * ((41674213 / 125000000000000000))) +
      6 * ((1387115217 / 1000000000000000000)) * ((41674213 / 125000000000000000)) * (126 / 100) + 8 * ((41674213 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13204 166) (d.f1 13204 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13204 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13204 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13204 166) (d.f1 13204 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13204 166) (d.w1 13204 166) (d.w2 13204 166)
  have hwexpr0 : 0 ≤ d.w0 13204 166 + d.w1 13204 166 * √(π / 2) +
      2 * d.w2 13204 166 + energyR16 13204 *
      radiusPolynomialRoot16 (d.w0 13204 166) (d.w1 13204 166) (d.w2 13204 166) := by
    positivity
  constructor
  · change (13204 : ℝ) ^ 8 * (mA 13204 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13204 166) (d.f1 13204 166) d.f2 + locationR16 13204 *
        radiusPolynomialRoot16 (d.f0 13204 166) (d.f1 13204 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13204 : ℝ) ^ 8 * (mA 13204 : ℝ) ^ 8 *
        ((((4157808133 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4157808133 / 1000000000000000000)) * ((1387115217 / 1000000000000000000)) * (126 / 100) +
          2 * (((1387115217 / 1000000000000000000)) ^ 2 + 2 * ((4157808133 / 1000000000000000000)) * ((41674213 / 125000000000000000))) +
          6 * ((1387115217 / 1000000000000000000)) * ((41674213 / 125000000000000000)) * (126 / 100) + 8 * ((41674213 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13204) *
          (32 * (((4157808133 / 1000000000000000000) : ℝ) + (1387115217 / 1000000000000000000) + (41674213 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13204 : ℝ) ^ 16 *
      (d.w0 13204 166 + d.w1 13204 166 * √(π / 2) + 2 * d.w2 13204 166 +
        energyR16 13204 * radiusPolynomialRoot16 (d.w0 13204 166) (d.w1 13204 166)
          (d.w2 13204 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13204 : ℝ) ^ 16 *
        (((1631178861 / 100000000000000000000) : ℝ) + ((580276323 / 50000000000000000000)) * (126 / 100) + 2 * ((212018021 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13204) *
          (32 * (((1631178861 / 100000000000000000000) : ℝ) + (580276323 / 50000000000000000000) + (212018021 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13204

/-! A coarse bound on the actual paper statistics constant at dimension 13205. -/
namespace BstLean.Part266.Row13205
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13203 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13203 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13203 128 ≤ (13457 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13457 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13205) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13205 : ℕ))
    (by norm_num : (13205 : ℕ) ≤ 16384)
  have ht : paperTail256 13205 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13205 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13205 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13205 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13205 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13205 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13203 128 * √(2 / (13205 : ℝ)) *
      (√(13205 : ℝ) + paperT0 13205 + paperTail256 13205) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13205 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13205 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13205 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13203 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13203 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13205 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13205

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13205
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13205 (61 / 100) 166 (17 / (100 * 13205)) (26 / (10 * 13205)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13205 (61 / 100) 166 (17 / (100 * 13205)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (105984021 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (128416839 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (748004311 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13205 / 13205 * (61 / 100)) ^ 4 * inverseRadius8 (13205 - 1) /
            envelopeGap 13205 (61 / 100) 166 (17 / (100 * 13205)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13205

namespace BstLean.Part266.Row13205
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13205 166 ≤ (1039255353 / 250000000000000000)
  f1 : (tableEnvelope C).f1 13205 166 ≤ (346713177 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (166665299 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13205 166 ≤ (815404189 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13205 166 ≤ (1160289033 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13205 166 ≤ (423939707 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (105984021 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (105984021 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (128416839 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (748004311 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3588023 / 1000000000) : ℝ) ≤ √(17 / (100 * 13205) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13205) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2058970821 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (35835295311 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13205) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13205) ≤ (4283873 / 40000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13205) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13205 * (166 : ℝ) ^ 2 + 26 / (10 * 13205) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13205) : ℝ)) (tA 13205 * 166 ^ 2 + 26 / (10 * 13205)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3588023 / 1000000000))) * ((105984021 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3588023 / 1000000000)) ^ 3) * ((128416839 / 100000000000000000000000))) + ((748004311 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3588023 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13205) : ℝ)) d.D d.V d.P (√(tA 13205) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3588023 / 1000000000)) ^ 2 * (((2058970821 / 1000000000000000)) * ((35835295311 / 1000000000000000000)))) + ((748004311 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13205) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3588023 / 1000000000)) * ((105984021 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13205) : ℝ)) (tA 13205 * 166 ^ 2 + 26 / (10 * 13205)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((105984021 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3588023 / 1000000000)) ^ 2) * ((128416839 / 100000000000000000000000)) + ((748004311 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13205) : ℝ)) (√(26 / (10 * 13205) : ℝ)) d.D d.V d.P (√(tA 13205) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3588023 / 1000000000)) * (((2058970821 / 1000000000000000)) * ((35835295311 / 1000000000000000000))) + ((748004311 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13205) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((105984021 / 25000000000000000000) : ℝ) + ((748004311 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13205

namespace BstLean.Part266.Row13205
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13205 166 ∧
    0 ≤ (tableEnvelope C).f1 13205 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13205 166 ∧
    0 ≤ (tableEnvelope C).w1 13205 166 ∧ 0 ≤ (tableEnvelope C).w2 13205 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13205 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13205 166 ∧ 0 ≤ d.f1 13205 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13205 166 ∧ 0 ≤ d.w1 13205 166 ∧ 0 ≤ d.w2 13205 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13205 ≤ 2 * (228 / 100 : ℝ) / 13205 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13205 ≤ 2 * (370 / 100 : ℝ) / 13205 := by
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
    (completeRAData (tableEnvelope C) 13205 166).locationBound 13205 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13205 166).energyBound 13205 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13205 166) (d.f1 13205 166) d.f2 ≤
      32 * (((1039255353 / 250000000000000000) : ℝ) + (346713177 / 250000000000000000) + (166665299 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13205 166) (d.w1 13205 166)
      (d.w2 13205 166) ≤
      32 * (((815404189 / 50000000000000000000) : ℝ) + (1160289033 / 100000000000000000000) + (423939707 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13205 166) (d.f1 13205 166) d.f2 ≤
      ((1039255353 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1039255353 / 250000000000000000)) * ((346713177 / 250000000000000000)) * (126 / 100) +
      2 * (((346713177 / 250000000000000000)) ^ 2 + 2 * ((1039255353 / 250000000000000000)) * ((166665299 / 500000000000000000))) +
      6 * ((346713177 / 250000000000000000)) * ((166665299 / 500000000000000000)) * (126 / 100) + 8 * ((166665299 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13205 166) (d.f1 13205 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13205 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13205 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13205 166) (d.f1 13205 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13205 166) (d.w1 13205 166) (d.w2 13205 166)
  have hwexpr0 : 0 ≤ d.w0 13205 166 + d.w1 13205 166 * √(π / 2) +
      2 * d.w2 13205 166 + energyR16 13205 *
      radiusPolynomialRoot16 (d.w0 13205 166) (d.w1 13205 166) (d.w2 13205 166) := by
    positivity
  constructor
  · change (13205 : ℝ) ^ 8 * (mA 13205 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13205 166) (d.f1 13205 166) d.f2 + locationR16 13205 *
        radiusPolynomialRoot16 (d.f0 13205 166) (d.f1 13205 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13205 : ℝ) ^ 8 * (mA 13205 : ℝ) ^ 8 *
        ((((1039255353 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1039255353 / 250000000000000000)) * ((346713177 / 250000000000000000)) * (126 / 100) +
          2 * (((346713177 / 250000000000000000)) ^ 2 + 2 * ((1039255353 / 250000000000000000)) * ((166665299 / 500000000000000000))) +
          6 * ((346713177 / 250000000000000000)) * ((166665299 / 500000000000000000)) * (126 / 100) + 8 * ((166665299 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13205) *
          (32 * (((1039255353 / 250000000000000000) : ℝ) + (346713177 / 250000000000000000) + (166665299 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13205 : ℝ) ^ 16 *
      (d.w0 13205 166 + d.w1 13205 166 * √(π / 2) + 2 * d.w2 13205 166 +
        energyR16 13205 * radiusPolynomialRoot16 (d.w0 13205 166) (d.w1 13205 166)
          (d.w2 13205 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13205 : ℝ) ^ 16 *
        (((815404189 / 50000000000000000000) : ℝ) + ((1160289033 / 100000000000000000000)) * (126 / 100) + 2 * ((423939707 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13205) *
          (32 * (((815404189 / 50000000000000000000) : ℝ) + (1160289033 / 100000000000000000000) + (423939707 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13205

/-! A coarse bound on the actual paper statistics constant at dimension 13206. -/
namespace BstLean.Part266.Row13206
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13204 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13204 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13204 128 ≤ (13458 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13458 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13206) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13206 : ℕ))
    (by norm_num : (13206 : ℕ) ≤ 16384)
  have ht : paperTail256 13206 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13206 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13206 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13206 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13206 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13206 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13204 128 * √(2 / (13206 : ℝ)) *
      (√(13206 : ℝ) + paperT0 13206 + paperTail256 13206) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13206 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13206 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13206 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13204 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13204 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13206 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13206

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13206
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13206 (61 / 100) 166 (17 / (100 * 13206)) (26 / (10 * 13206)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13206 (61 / 100) 166 (17 / (100 * 13206)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (423839781 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (641889727 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (74754707 / 20000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13206 / 13206 * (61 / 100)) ^ 4 * inverseRadius8 (13206 - 1) /
            envelopeGap 13206 (61 / 100) 166 (17 / (100 * 13206)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13206

namespace BstLean.Part266.Row13206
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13206 166 ≤ (83124699 / 20000000000000000)
  f1 : (tableEnvelope C).f1 13206 166 ≤ (34664757 / 25000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (333267509 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13206 166 ≤ (1630438017 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13206 166 ≤ (580012753 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13206 166 ≤ (211921701 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (423839781 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (423839781 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (641889727 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (74754707 / 20000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3587887 / 1000000000) : ℝ) ≤ √(17 / (100 * 13206) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13206) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1029368473 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (35829868183 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13206) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13206) ≤ (21417743 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13206) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13206 * (166 : ℝ) ^ 2 + 26 / (10 * 13206) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13206) : ℝ)) (tA 13206 * 166 ^ 2 + 26 / (10 * 13206)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3587887 / 1000000000))) * ((423839781 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3587887 / 1000000000)) ^ 3) * ((641889727 / 500000000000000000000000))) + ((74754707 / 20000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3587887 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13206) : ℝ)) d.D d.V d.P (√(tA 13206) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3587887 / 1000000000)) ^ 2 * (((1029368473 / 500000000000000)) * ((35829868183 / 1000000000000000000)))) + ((74754707 / 20000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13206) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3587887 / 1000000000)) * ((423839781 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13206) : ℝ)) (tA 13206 * 166 ^ 2 + 26 / (10 * 13206)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((423839781 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3587887 / 1000000000)) ^ 2) * ((641889727 / 500000000000000000000000)) + ((74754707 / 20000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13206) : ℝ)) (√(26 / (10 * 13206) : ℝ)) d.D d.V d.P (√(tA 13206) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3587887 / 1000000000)) * (((1029368473 / 500000000000000)) * ((35829868183 / 1000000000000000000))) + ((74754707 / 20000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13206) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((423839781 / 100000000000000000000) : ℝ) + ((74754707 / 20000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13206

namespace BstLean.Part266.Row13206
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13206 166 ∧
    0 ≤ (tableEnvelope C).f1 13206 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13206 166 ∧
    0 ≤ (tableEnvelope C).w1 13206 166 ∧ 0 ≤ (tableEnvelope C).w2 13206 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13206 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13206 166 ∧ 0 ≤ d.f1 13206 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13206 166 ∧ 0 ≤ d.w1 13206 166 ∧ 0 ≤ d.w2 13206 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13206 ≤ 2 * (228 / 100 : ℝ) / 13206 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13206 ≤ 2 * (370 / 100 : ℝ) / 13206 := by
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
    (completeRAData (tableEnvelope C) 13206 166).locationBound 13206 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13206 166).energyBound 13206 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13206 166) (d.f1 13206 166) d.f2 ≤
      32 * (((83124699 / 20000000000000000) : ℝ) + (34664757 / 25000000000000000) + (333267509 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13206 166) (d.w1 13206 166)
      (d.w2 13206 166) ≤
      32 * (((1630438017 / 100000000000000000000) : ℝ) + (580012753 / 50000000000000000000) + (211921701 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13206 166) (d.f1 13206 166) d.f2 ≤
      ((83124699 / 20000000000000000) : ℝ) ^ 2 + 2 * ((83124699 / 20000000000000000)) * ((34664757 / 25000000000000000)) * (126 / 100) +
      2 * (((34664757 / 25000000000000000)) ^ 2 + 2 * ((83124699 / 20000000000000000)) * ((333267509 / 1000000000000000000))) +
      6 * ((34664757 / 25000000000000000)) * ((333267509 / 1000000000000000000)) * (126 / 100) + 8 * ((333267509 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13206 166) (d.f1 13206 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13206 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13206 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13206 166) (d.f1 13206 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13206 166) (d.w1 13206 166) (d.w2 13206 166)
  have hwexpr0 : 0 ≤ d.w0 13206 166 + d.w1 13206 166 * √(π / 2) +
      2 * d.w2 13206 166 + energyR16 13206 *
      radiusPolynomialRoot16 (d.w0 13206 166) (d.w1 13206 166) (d.w2 13206 166) := by
    positivity
  constructor
  · change (13206 : ℝ) ^ 8 * (mA 13206 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13206 166) (d.f1 13206 166) d.f2 + locationR16 13206 *
        radiusPolynomialRoot16 (d.f0 13206 166) (d.f1 13206 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13206 : ℝ) ^ 8 * (mA 13206 : ℝ) ^ 8 *
        ((((83124699 / 20000000000000000) : ℝ) ^ 2 + 2 * ((83124699 / 20000000000000000)) * ((34664757 / 25000000000000000)) * (126 / 100) +
          2 * (((34664757 / 25000000000000000)) ^ 2 + 2 * ((83124699 / 20000000000000000)) * ((333267509 / 1000000000000000000))) +
          6 * ((34664757 / 25000000000000000)) * ((333267509 / 1000000000000000000)) * (126 / 100) + 8 * ((333267509 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13206) *
          (32 * (((83124699 / 20000000000000000) : ℝ) + (34664757 / 25000000000000000) + (333267509 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13206 : ℝ) ^ 16 *
      (d.w0 13206 166 + d.w1 13206 166 * √(π / 2) + 2 * d.w2 13206 166 +
        energyR16 13206 * radiusPolynomialRoot16 (d.w0 13206 166) (d.w1 13206 166)
          (d.w2 13206 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13206 : ℝ) ^ 16 *
        (((1630438017 / 100000000000000000000) : ℝ) + ((580012753 / 50000000000000000000)) * (126 / 100) + 2 * ((211921701 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13206) *
          (32 * (((1630438017 / 100000000000000000000) : ℝ) + (580012753 / 50000000000000000000) + (211921701 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13206

/-! A coarse bound on the actual paper statistics constant at dimension 13207. -/
namespace BstLean.Part266.Row13207
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13205 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13205 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13205 128 ≤ (13459 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13459 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13207) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13207 : ℕ))
    (by norm_num : (13207 : ℕ) ≤ 16384)
  have ht : paperTail256 13207 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13207 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13207 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13207 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13207 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13207 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13205 128 * √(2 / (13207 : ℝ)) *
      (√(13207 : ℝ) + paperT0 13207 + paperTail256 13207) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13207 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13207 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13207 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13205 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13205 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13207 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13207

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13207
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13207 (61 / 100) 166 (17 / (100 * 13207)) (26 / (10 * 13207)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13207 (61 / 100) 166 (17 / (100 * 13207)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (423743507 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (256678133 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3735450719 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13207 / 13207 * (61 / 100)) ^ 4 * inverseRadius8 (13207 - 1) /
            envelopeGap 13207 (61 / 100) 166 (17 / (100 * 13207)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13207

namespace BstLean.Part266.Row13207
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13207 166 ≤ (4155448747 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13207 166 ≤ (346581983 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (333204439 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13207 166 ≤ (815033889 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13207 166 ≤ (579881031 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13207 166 ≤ (211873563 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (423743507 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (423743507 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (256678133 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3735450719 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3587751 / 1000000000) : ℝ) ≤ √(17 / (100 * 13207) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13207) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1029251557 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7164888457 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13207) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13207) ≤ (53540303 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13207) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13207 * (166 : ℝ) ^ 2 + 26 / (10 * 13207) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13207) : ℝ)) (tA 13207 * 166 ^ 2 + 26 / (10 * 13207)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3587751 / 1000000000))) * ((423743507 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3587751 / 1000000000)) ^ 3) * ((256678133 / 200000000000000000000000))) + ((3735450719 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3587751 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13207) : ℝ)) d.D d.V d.P (√(tA 13207) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3587751 / 1000000000)) ^ 2 * (((1029251557 / 500000000000000)) * ((7164888457 / 200000000000000000)))) + ((3735450719 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13207) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3587751 / 1000000000)) * ((423743507 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13207) : ℝ)) (tA 13207 * 166 ^ 2 + 26 / (10 * 13207)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((423743507 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3587751 / 1000000000)) ^ 2) * ((256678133 / 200000000000000000000000)) + ((3735450719 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13207) : ℝ)) (√(26 / (10 * 13207) : ℝ)) d.D d.V d.P (√(tA 13207) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3587751 / 1000000000)) * (((1029251557 / 500000000000000)) * ((7164888457 / 200000000000000000))) + ((3735450719 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13207) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((423743507 / 100000000000000000000) : ℝ) + ((3735450719 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13207

namespace BstLean.Part266.Row13207
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13207 166 ∧
    0 ≤ (tableEnvelope C).f1 13207 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13207 166 ∧
    0 ≤ (tableEnvelope C).w1 13207 166 ∧ 0 ≤ (tableEnvelope C).w2 13207 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13207 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13207 166 ∧ 0 ≤ d.f1 13207 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13207 166 ∧ 0 ≤ d.w1 13207 166 ∧ 0 ≤ d.w2 13207 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13207 ≤ 2 * (228 / 100 : ℝ) / 13207 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13207 ≤ 2 * (370 / 100 : ℝ) / 13207 := by
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
    (completeRAData (tableEnvelope C) 13207 166).locationBound 13207 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13207 166).energyBound 13207 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13207 166) (d.f1 13207 166) d.f2 ≤
      32 * (((4155448747 / 1000000000000000000) : ℝ) + (346581983 / 250000000000000000) + (333204439 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13207 166) (d.w1 13207 166)
      (d.w2 13207 166) ≤
      32 * (((815033889 / 50000000000000000000) : ℝ) + (579881031 / 50000000000000000000) + (211873563 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13207 166) (d.f1 13207 166) d.f2 ≤
      ((4155448747 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4155448747 / 1000000000000000000)) * ((346581983 / 250000000000000000)) * (126 / 100) +
      2 * (((346581983 / 250000000000000000)) ^ 2 + 2 * ((4155448747 / 1000000000000000000)) * ((333204439 / 1000000000000000000))) +
      6 * ((346581983 / 250000000000000000)) * ((333204439 / 1000000000000000000)) * (126 / 100) + 8 * ((333204439 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13207 166) (d.f1 13207 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13207 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13207 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13207 166) (d.f1 13207 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13207 166) (d.w1 13207 166) (d.w2 13207 166)
  have hwexpr0 : 0 ≤ d.w0 13207 166 + d.w1 13207 166 * √(π / 2) +
      2 * d.w2 13207 166 + energyR16 13207 *
      radiusPolynomialRoot16 (d.w0 13207 166) (d.w1 13207 166) (d.w2 13207 166) := by
    positivity
  constructor
  · change (13207 : ℝ) ^ 8 * (mA 13207 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13207 166) (d.f1 13207 166) d.f2 + locationR16 13207 *
        radiusPolynomialRoot16 (d.f0 13207 166) (d.f1 13207 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13207 : ℝ) ^ 8 * (mA 13207 : ℝ) ^ 8 *
        ((((4155448747 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4155448747 / 1000000000000000000)) * ((346581983 / 250000000000000000)) * (126 / 100) +
          2 * (((346581983 / 250000000000000000)) ^ 2 + 2 * ((4155448747 / 1000000000000000000)) * ((333204439 / 1000000000000000000))) +
          6 * ((346581983 / 250000000000000000)) * ((333204439 / 1000000000000000000)) * (126 / 100) + 8 * ((333204439 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13207) *
          (32 * (((4155448747 / 1000000000000000000) : ℝ) + (346581983 / 250000000000000000) + (333204439 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13207 : ℝ) ^ 16 *
      (d.w0 13207 166 + d.w1 13207 166 * √(π / 2) + 2 * d.w2 13207 166 +
        energyR16 13207 * radiusPolynomialRoot16 (d.w0 13207 166) (d.w1 13207 166)
          (d.w2 13207 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13207 : ℝ) ^ 16 *
        (((815033889 / 50000000000000000000) : ℝ) + ((579881031 / 50000000000000000000)) * (126 / 100) + 2 * ((211873563 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13207) *
          (32 * (((815033889 / 50000000000000000000) : ℝ) + (579881031 / 50000000000000000000) + (211873563 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13207

/-! A coarse bound on the actual paper statistics constant at dimension 13208. -/
namespace BstLean.Part266.Row13208
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13206 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13206 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13206 128 ≤ (13460 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13460 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13208) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13208 : ℕ))
    (by norm_num : (13208 : ℕ) ≤ 16384)
  have ht : paperTail256 13208 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13208 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13208 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13208 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13208 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13208 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13206 128 * √(2 / (13208 : ℝ)) *
      (√(13208 : ℝ) + paperT0 13208 + paperTail256 13208) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13208 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13208 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13208 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13206 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13206 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13208 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13208

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13208
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13208 (61 / 100) 166 (17 / (100 * 13208)) (26 / (10 * 13208)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13208 (61 / 100) 166 (17 / (100 * 13208)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (423647263 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (160375253 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (186658383 / 50000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13208 / 13208 * (61 / 100)) ^ 4 * inverseRadius8 (13208 - 1) /
            envelopeGap 13208 (61 / 100) 166 (17 / (100 * 13208)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13208

namespace BstLean.Part266.Row13208
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13208 166 ≤ (4154662807 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13208 166 ≤ (346516417 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (333141387 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13208 166 ≤ (1629697663 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13208 166 ≤ (231899741 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 13208 166 ≤ (1323909 / 312500000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (423647263 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (423647263 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (160375253 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (186658383 / 50000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((717523 / 200000000) : ℝ) ≤ √(17 / (100 * 13208) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13208) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2058269329 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (35819017631 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13208) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13208) ≤ (107072499 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13208) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13208 * (166 : ℝ) ^ 2 + 26 / (10 * 13208) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13208) : ℝ)) (tA 13208 * 166 ^ 2 + 26 / (10 * 13208)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((717523 / 200000000))) * ((423647263 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((717523 / 200000000)) ^ 3) * ((160375253 / 125000000000000000000000))) + ((186658383 / 50000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((717523 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13208) : ℝ)) d.D d.V d.P (√(tA 13208) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((717523 / 200000000)) ^ 2 * (((2058269329 / 1000000000000000)) * ((35819017631 / 1000000000000000000)))) + ((186658383 / 50000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13208) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((717523 / 200000000)) * ((423647263 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13208) : ℝ)) (tA 13208 * 166 ^ 2 + 26 / (10 * 13208)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((423647263 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((717523 / 200000000)) ^ 2) * ((160375253 / 125000000000000000000000)) + ((186658383 / 50000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13208) : ℝ)) (√(26 / (10 * 13208) : ℝ)) d.D d.V d.P (√(tA 13208) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((717523 / 200000000)) * (((2058269329 / 1000000000000000)) * ((35819017631 / 1000000000000000000))) + ((186658383 / 50000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13208) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((423647263 / 100000000000000000000) : ℝ) + ((186658383 / 50000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13208

namespace BstLean.Part266.Row13208
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13208 166 ∧
    0 ≤ (tableEnvelope C).f1 13208 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13208 166 ∧
    0 ≤ (tableEnvelope C).w1 13208 166 ∧ 0 ≤ (tableEnvelope C).w2 13208 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13208 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13208 166 ∧ 0 ≤ d.f1 13208 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13208 166 ∧ 0 ≤ d.w1 13208 166 ∧ 0 ≤ d.w2 13208 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13208 ≤ 2 * (228 / 100 : ℝ) / 13208 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13208 ≤ 2 * (370 / 100 : ℝ) / 13208 := by
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
    (completeRAData (tableEnvelope C) 13208 166).locationBound 13208 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13208 166).energyBound 13208 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13208 166) (d.f1 13208 166) d.f2 ≤
      32 * (((4154662807 / 1000000000000000000) : ℝ) + (346516417 / 250000000000000000) + (333141387 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13208 166) (d.w1 13208 166)
      (d.w2 13208 166) ≤
      32 * (((1629697663 / 100000000000000000000) : ℝ) + (231899741 / 20000000000000000000) + (1323909 / 312500000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13208 166) (d.f1 13208 166) d.f2 ≤
      ((4154662807 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4154662807 / 1000000000000000000)) * ((346516417 / 250000000000000000)) * (126 / 100) +
      2 * (((346516417 / 250000000000000000)) ^ 2 + 2 * ((4154662807 / 1000000000000000000)) * ((333141387 / 1000000000000000000))) +
      6 * ((346516417 / 250000000000000000)) * ((333141387 / 1000000000000000000)) * (126 / 100) + 8 * ((333141387 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13208 166) (d.f1 13208 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13208 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13208 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13208 166) (d.f1 13208 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13208 166) (d.w1 13208 166) (d.w2 13208 166)
  have hwexpr0 : 0 ≤ d.w0 13208 166 + d.w1 13208 166 * √(π / 2) +
      2 * d.w2 13208 166 + energyR16 13208 *
      radiusPolynomialRoot16 (d.w0 13208 166) (d.w1 13208 166) (d.w2 13208 166) := by
    positivity
  constructor
  · change (13208 : ℝ) ^ 8 * (mA 13208 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13208 166) (d.f1 13208 166) d.f2 + locationR16 13208 *
        radiusPolynomialRoot16 (d.f0 13208 166) (d.f1 13208 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13208 : ℝ) ^ 8 * (mA 13208 : ℝ) ^ 8 *
        ((((4154662807 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4154662807 / 1000000000000000000)) * ((346516417 / 250000000000000000)) * (126 / 100) +
          2 * (((346516417 / 250000000000000000)) ^ 2 + 2 * ((4154662807 / 1000000000000000000)) * ((333141387 / 1000000000000000000))) +
          6 * ((346516417 / 250000000000000000)) * ((333141387 / 1000000000000000000)) * (126 / 100) + 8 * ((333141387 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13208) *
          (32 * (((4154662807 / 1000000000000000000) : ℝ) + (346516417 / 250000000000000000) + (333141387 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13208 : ℝ) ^ 16 *
      (d.w0 13208 166 + d.w1 13208 166 * √(π / 2) + 2 * d.w2 13208 166 +
        energyR16 13208 * radiusPolynomialRoot16 (d.w0 13208 166) (d.w1 13208 166)
          (d.w2 13208 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13208 : ℝ) ^ 16 *
        (((1629697663 / 100000000000000000000) : ℝ) + ((231899741 / 20000000000000000000)) * (126 / 100) + 2 * ((1323909 / 312500000000000000)) +
          (2 * (370 / 100 : ℝ) / 13208) *
          (32 * (((1629697663 / 100000000000000000000) : ℝ) + (231899741 / 20000000000000000000) + (1323909 / 312500000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13208

/-! A coarse bound on the actual paper statistics constant at dimension 13209. -/
namespace BstLean.Part266.Row13209
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13207 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13207 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13207 128 ≤ (13461 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13461 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13209) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13209 : ℕ))
    (by norm_num : (13209 : ℕ) ≤ 16384)
  have ht : paperTail256 13209 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13209 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13209 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13209 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13209 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13209 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13207 128 * √(2 / (13209 : ℝ)) *
      (√(13209 : ℝ) + paperT0 13209 + paperTail256 13209) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13209 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13209 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13209 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13207 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13207 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13209 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13209

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13209
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13209 (61 / 100) 166 (17 / (100 * 13209)) (26 / (10 * 13209)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13209 (61 / 100) 166 (17 / (100 * 13209)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (423551047 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (128261353 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (932721543 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13209 / 13209 * (61 / 100)) ^ 4 * inverseRadius8 (13209 - 1) /
            envelopeGap 13209 (61 / 100) 166 (17 / (100 * 13209)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13209

namespace BstLean.Part266.Row13209
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13209 166 ≤ (4153873783 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13209 166 ≤ (173225339 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (16653913 / 50000000000000000)
  w0 : (tableEnvelope C).w0 13209 166 ≤ (814663499 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13209 166 ≤ (289808777 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 13209 166 ≤ (211777331 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (423551047 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (423551047 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (128261353 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (932721543 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((89687 / 25000000) : ℝ) ≤ √(17 / (100 * 13209) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13209) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1029017793 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (35813594207 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13209) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13209) ≤ (107064393 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13209) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13209 * (166 : ℝ) ^ 2 + 26 / (10 * 13209) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13209) : ℝ)) (tA 13209 * 166 ^ 2 + 26 / (10 * 13209)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((89687 / 25000000))) * ((423551047 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((89687 / 25000000)) ^ 3) * ((128261353 / 100000000000000000000000))) + ((932721543 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((89687 / 25000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13209) : ℝ)) d.D d.V d.P (√(tA 13209) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((89687 / 25000000)) ^ 2 * (((1029017793 / 500000000000000)) * ((35813594207 / 1000000000000000000)))) + ((932721543 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13209) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((89687 / 25000000)) * ((423551047 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13209) : ℝ)) (tA 13209 * 166 ^ 2 + 26 / (10 * 13209)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((423551047 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((89687 / 25000000)) ^ 2) * ((128261353 / 100000000000000000000000)) + ((932721543 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13209) : ℝ)) (√(26 / (10 * 13209) : ℝ)) d.D d.V d.P (√(tA 13209) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((89687 / 25000000)) * (((1029017793 / 500000000000000)) * ((35813594207 / 1000000000000000000))) + ((932721543 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13209) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((423551047 / 100000000000000000000) : ℝ) + ((932721543 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13209

namespace BstLean.Part266.Row13209
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13209 166 ∧
    0 ≤ (tableEnvelope C).f1 13209 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13209 166 ∧
    0 ≤ (tableEnvelope C).w1 13209 166 ∧ 0 ≤ (tableEnvelope C).w2 13209 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13209 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13209 166 ∧ 0 ≤ d.f1 13209 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13209 166 ∧ 0 ≤ d.w1 13209 166 ∧ 0 ≤ d.w2 13209 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13209 ≤ 2 * (228 / 100 : ℝ) / 13209 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13209 ≤ 2 * (370 / 100 : ℝ) / 13209 := by
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
    (completeRAData (tableEnvelope C) 13209 166).locationBound 13209 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13209 166).energyBound 13209 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13209 166) (d.f1 13209 166) d.f2 ≤
      32 * (((4153873783 / 1000000000000000000) : ℝ) + (173225339 / 125000000000000000) + (16653913 / 50000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13209 166) (d.w1 13209 166)
      (d.w2 13209 166) ≤
      32 * (((814663499 / 50000000000000000000) : ℝ) + (289808777 / 25000000000000000000) + (211777331 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13209 166) (d.f1 13209 166) d.f2 ≤
      ((4153873783 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4153873783 / 1000000000000000000)) * ((173225339 / 125000000000000000)) * (126 / 100) +
      2 * (((173225339 / 125000000000000000)) ^ 2 + 2 * ((4153873783 / 1000000000000000000)) * ((16653913 / 50000000000000000))) +
      6 * ((173225339 / 125000000000000000)) * ((16653913 / 50000000000000000)) * (126 / 100) + 8 * ((16653913 / 50000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13209 166) (d.f1 13209 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13209 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13209 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13209 166) (d.f1 13209 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13209 166) (d.w1 13209 166) (d.w2 13209 166)
  have hwexpr0 : 0 ≤ d.w0 13209 166 + d.w1 13209 166 * √(π / 2) +
      2 * d.w2 13209 166 + energyR16 13209 *
      radiusPolynomialRoot16 (d.w0 13209 166) (d.w1 13209 166) (d.w2 13209 166) := by
    positivity
  constructor
  · change (13209 : ℝ) ^ 8 * (mA 13209 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13209 166) (d.f1 13209 166) d.f2 + locationR16 13209 *
        radiusPolynomialRoot16 (d.f0 13209 166) (d.f1 13209 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13209 : ℝ) ^ 8 * (mA 13209 : ℝ) ^ 8 *
        ((((4153873783 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4153873783 / 1000000000000000000)) * ((173225339 / 125000000000000000)) * (126 / 100) +
          2 * (((173225339 / 125000000000000000)) ^ 2 + 2 * ((4153873783 / 1000000000000000000)) * ((16653913 / 50000000000000000))) +
          6 * ((173225339 / 125000000000000000)) * ((16653913 / 50000000000000000)) * (126 / 100) + 8 * ((16653913 / 50000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13209) *
          (32 * (((4153873783 / 1000000000000000000) : ℝ) + (173225339 / 125000000000000000) + (16653913 / 50000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13209 : ℝ) ^ 16 *
      (d.w0 13209 166 + d.w1 13209 166 * √(π / 2) + 2 * d.w2 13209 166 +
        energyR16 13209 * radiusPolynomialRoot16 (d.w0 13209 166) (d.w1 13209 166)
          (d.w2 13209 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13209 : ℝ) ^ 16 *
        (((814663499 / 50000000000000000000) : ℝ) + ((289808777 / 25000000000000000000)) * (126 / 100) + 2 * ((211777331 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13209) *
          (32 * (((814663499 / 50000000000000000000) : ℝ) + (289808777 / 25000000000000000000) + (211777331 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13209

/-! A coarse bound on the actual paper statistics constant at dimension 13210. -/
namespace BstLean.Part266.Row13210
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13208 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13208 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13208 128 ≤ (13462 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13462 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13210) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13210 : ℕ))
    (by norm_num : (13210 : ℕ) ≤ 16384)
  have ht : paperTail256 13210 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13210 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13210 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13210 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13210 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13210 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13208 128 * √(2 / (13210 : ℝ)) *
      (√(13210 : ℝ) + paperT0 13210 + paperTail256 13210) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13210 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13210 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13210 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13208 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13208 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13210 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13210

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13210
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13210 (61 / 100) 166 (17 / (100 * 13210)) (26 / (10 * 13210)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13210 (61 / 100) 166 (17 / (100 * 13210)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (423454861 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1282225183 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1864303127 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13210 / 13210 * (61 / 100)) ^ 4 * inverseRadius8 (13210 - 1) /
            envelopeGap 13210 (61 / 100) 166 (17 / (100 * 13210)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13210

namespace BstLean.Part266.Row13210
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13210 166 ≤ (4153088363 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13210 166 ≤ (138554061 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (83253811 / 250000000000000000)
  w0 : (tableEnvelope C).w0 13210 166 ≤ (203619641 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 13210 166 ≤ (14487149 / 1250000000000000000)
  w2 : (tableEnvelope C).w2 13210 166 ≤ (423458473 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (423454861 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (423454861 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1282225183 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1864303127 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((224209 / 62500000) : ℝ) ≤ √(17 / (100 * 13210) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13210) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (64306309 / 31250000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7161634403 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13210) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13210) ≤ (3345509 / 31250000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13210) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13210 * (166 : ℝ) ^ 2 + 26 / (10 * 13210) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13210) : ℝ)) (tA 13210 * 166 ^ 2 + 26 / (10 * 13210)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((224209 / 62500000))) * ((423454861 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((224209 / 62500000)) ^ 3) * ((1282225183 / 1000000000000000000000000))) + ((1864303127 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((224209 / 62500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13210) : ℝ)) d.D d.V d.P (√(tA 13210) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((224209 / 62500000)) ^ 2 * (((64306309 / 31250000000000)) * ((7161634403 / 200000000000000000)))) + ((1864303127 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13210) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((224209 / 62500000)) * ((423454861 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13210) : ℝ)) (tA 13210 * 166 ^ 2 + 26 / (10 * 13210)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((423454861 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((224209 / 62500000)) ^ 2) * ((1282225183 / 1000000000000000000000000)) + ((1864303127 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13210) : ℝ)) (√(26 / (10 * 13210) : ℝ)) d.D d.V d.P (√(tA 13210) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((224209 / 62500000)) * (((64306309 / 31250000000000)) * ((7161634403 / 200000000000000000))) + ((1864303127 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13210) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((423454861 / 100000000000000000000) : ℝ) + ((1864303127 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13210

namespace BstLean.Part266.Row13210
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13210 166 ∧
    0 ≤ (tableEnvelope C).f1 13210 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13210 166 ∧
    0 ≤ (tableEnvelope C).w1 13210 166 ∧ 0 ≤ (tableEnvelope C).w2 13210 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13210 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13210 166 ∧ 0 ≤ d.f1 13210 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13210 166 ∧ 0 ≤ d.w1 13210 166 ∧ 0 ≤ d.w2 13210 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13210 ≤ 2 * (228 / 100 : ℝ) / 13210 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13210 ≤ 2 * (370 / 100 : ℝ) / 13210 := by
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
    (completeRAData (tableEnvelope C) 13210 166).locationBound 13210 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13210 166).energyBound 13210 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13210 166) (d.f1 13210 166) d.f2 ≤
      32 * (((4153088363 / 1000000000000000000) : ℝ) + (138554061 / 100000000000000000) + (83253811 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13210 166) (d.w1 13210 166)
      (d.w2 13210 166) ≤
      32 * (((203619641 / 12500000000000000000) : ℝ) + (14487149 / 1250000000000000000) + (423458473 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13210 166) (d.f1 13210 166) d.f2 ≤
      ((4153088363 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4153088363 / 1000000000000000000)) * ((138554061 / 100000000000000000)) * (126 / 100) +
      2 * (((138554061 / 100000000000000000)) ^ 2 + 2 * ((4153088363 / 1000000000000000000)) * ((83253811 / 250000000000000000))) +
      6 * ((138554061 / 100000000000000000)) * ((83253811 / 250000000000000000)) * (126 / 100) + 8 * ((83253811 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13210 166) (d.f1 13210 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13210 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13210 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13210 166) (d.f1 13210 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13210 166) (d.w1 13210 166) (d.w2 13210 166)
  have hwexpr0 : 0 ≤ d.w0 13210 166 + d.w1 13210 166 * √(π / 2) +
      2 * d.w2 13210 166 + energyR16 13210 *
      radiusPolynomialRoot16 (d.w0 13210 166) (d.w1 13210 166) (d.w2 13210 166) := by
    positivity
  constructor
  · change (13210 : ℝ) ^ 8 * (mA 13210 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13210 166) (d.f1 13210 166) d.f2 + locationR16 13210 *
        radiusPolynomialRoot16 (d.f0 13210 166) (d.f1 13210 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13210 : ℝ) ^ 8 * (mA 13210 : ℝ) ^ 8 *
        ((((4153088363 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4153088363 / 1000000000000000000)) * ((138554061 / 100000000000000000)) * (126 / 100) +
          2 * (((138554061 / 100000000000000000)) ^ 2 + 2 * ((4153088363 / 1000000000000000000)) * ((83253811 / 250000000000000000))) +
          6 * ((138554061 / 100000000000000000)) * ((83253811 / 250000000000000000)) * (126 / 100) + 8 * ((83253811 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13210) *
          (32 * (((4153088363 / 1000000000000000000) : ℝ) + (138554061 / 100000000000000000) + (83253811 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13210 : ℝ) ^ 16 *
      (d.w0 13210 166 + d.w1 13210 166 * √(π / 2) + 2 * d.w2 13210 166 +
        energyR16 13210 * radiusPolynomialRoot16 (d.w0 13210 166) (d.w1 13210 166)
          (d.w2 13210 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13210 : ℝ) ^ 16 *
        (((203619641 / 12500000000000000000) : ℝ) + ((14487149 / 1250000000000000000)) * (126 / 100) + 2 * ((423458473 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13210) *
          (32 * (((203619641 / 12500000000000000000) : ℝ) + (14487149 / 1250000000000000000) + (423458473 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13210

/-! A coarse bound on the actual paper statistics constant at dimension 13211. -/
namespace BstLean.Part266.Row13211
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13209 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13209 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13209 128 ≤ (13463 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13463 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13211) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13211 : ℕ))
    (by norm_num : (13211 : ℕ) ≤ 16384)
  have ht : paperTail256 13211 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13211 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13211 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13211 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13211 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13211 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13209 128 * √(2 / (13211 : ℝ)) *
      (√(13211 : ℝ) + paperT0 13211 + paperTail256 13211) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13211 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13211 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13211 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13209 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13209 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13211 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13211

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13211
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13211 (61 / 100) 166 (17 / (100 * 13211)) (26 / (10 * 13211)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13211 (61 / 100) 166 (17 / (100 * 13211)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (26459919 / 6250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1281836983 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1863163953 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13211 / 13211 * (61 / 100)) ^ 4 * inverseRadius8 (13211 - 1) /
            envelopeGap 13211 (61 / 100) 166 (17 / (100 * 13211)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13211

namespace BstLean.Part266.Row13211
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13211 166 ≤ (2076151601 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13211 166 ≤ (1385278589 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (166476123 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13211 166 ≤ (81429369 / 5000000000000000000)
  w1 : (tableEnvelope C).w1 13211 166 ≤ (72419301 / 6250000000000000000)
  w2 : (tableEnvelope C).w2 13211 166 ≤ (211681157 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (26459919 / 6250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (26459919 / 6250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1281836983 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1863163953 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((448401 / 125000000) : ℝ) ≤ √(17 / (100 * 13211) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13211) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (411513647 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (17901375527 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13211) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13211) ≤ (21409637 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13211) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13211 * (166 : ℝ) ^ 2 + 26 / (10 * 13211) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13211) : ℝ)) (tA 13211 * 166 ^ 2 + 26 / (10 * 13211)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((448401 / 125000000))) * ((26459919 / 6250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((448401 / 125000000)) ^ 3) * ((1281836983 / 1000000000000000000000000))) + ((1863163953 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((448401 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13211) : ℝ)) d.D d.V d.P (√(tA 13211) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((448401 / 125000000)) ^ 2 * (((411513647 / 200000000000000)) * ((17901375527 / 500000000000000000)))) + ((1863163953 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13211) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((448401 / 125000000)) * ((26459919 / 6250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13211) : ℝ)) (tA 13211 * 166 ^ 2 + 26 / (10 * 13211)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((26459919 / 6250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((448401 / 125000000)) ^ 2) * ((1281836983 / 1000000000000000000000000)) + ((1863163953 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13211) : ℝ)) (√(26 / (10 * 13211) : ℝ)) d.D d.V d.P (√(tA 13211) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((448401 / 125000000)) * (((411513647 / 200000000000000)) * ((17901375527 / 500000000000000000))) + ((1863163953 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13211) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((26459919 / 6250000000000000000) : ℝ) + ((1863163953 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13211

namespace BstLean.Part266.Row13211
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13211 166 ∧
    0 ≤ (tableEnvelope C).f1 13211 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13211 166 ∧
    0 ≤ (tableEnvelope C).w1 13211 166 ∧ 0 ≤ (tableEnvelope C).w2 13211 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13211 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13211 166 ∧ 0 ≤ d.f1 13211 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13211 166 ∧ 0 ≤ d.w1 13211 166 ∧ 0 ≤ d.w2 13211 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13211 ≤ 2 * (228 / 100 : ℝ) / 13211 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13211 ≤ 2 * (370 / 100 : ℝ) / 13211 := by
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
    (completeRAData (tableEnvelope C) 13211 166).locationBound 13211 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13211 166).energyBound 13211 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13211 166) (d.f1 13211 166) d.f2 ≤
      32 * (((2076151601 / 500000000000000000) : ℝ) + (1385278589 / 1000000000000000000) + (166476123 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13211 166) (d.w1 13211 166)
      (d.w2 13211 166) ≤
      32 * (((81429369 / 5000000000000000000) : ℝ) + (72419301 / 6250000000000000000) + (211681157 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13211 166) (d.f1 13211 166) d.f2 ≤
      ((2076151601 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2076151601 / 500000000000000000)) * ((1385278589 / 1000000000000000000)) * (126 / 100) +
      2 * (((1385278589 / 1000000000000000000)) ^ 2 + 2 * ((2076151601 / 500000000000000000)) * ((166476123 / 500000000000000000))) +
      6 * ((1385278589 / 1000000000000000000)) * ((166476123 / 500000000000000000)) * (126 / 100) + 8 * ((166476123 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13211 166) (d.f1 13211 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13211 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13211 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13211 166) (d.f1 13211 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13211 166) (d.w1 13211 166) (d.w2 13211 166)
  have hwexpr0 : 0 ≤ d.w0 13211 166 + d.w1 13211 166 * √(π / 2) +
      2 * d.w2 13211 166 + energyR16 13211 *
      radiusPolynomialRoot16 (d.w0 13211 166) (d.w1 13211 166) (d.w2 13211 166) := by
    positivity
  constructor
  · change (13211 : ℝ) ^ 8 * (mA 13211 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13211 166) (d.f1 13211 166) d.f2 + locationR16 13211 *
        radiusPolynomialRoot16 (d.f0 13211 166) (d.f1 13211 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13211 : ℝ) ^ 8 * (mA 13211 : ℝ) ^ 8 *
        ((((2076151601 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2076151601 / 500000000000000000)) * ((1385278589 / 1000000000000000000)) * (126 / 100) +
          2 * (((1385278589 / 1000000000000000000)) ^ 2 + 2 * ((2076151601 / 500000000000000000)) * ((166476123 / 500000000000000000))) +
          6 * ((1385278589 / 1000000000000000000)) * ((166476123 / 500000000000000000)) * (126 / 100) + 8 * ((166476123 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13211) *
          (32 * (((2076151601 / 500000000000000000) : ℝ) + (1385278589 / 1000000000000000000) + (166476123 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13211 : ℝ) ^ 16 *
      (d.w0 13211 166 + d.w1 13211 166 * √(π / 2) + 2 * d.w2 13211 166 +
        energyR16 13211 * radiusPolynomialRoot16 (d.w0 13211 166) (d.w1 13211 166)
          (d.w2 13211 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13211 : ℝ) ^ 16 *
        (((81429369 / 5000000000000000000) : ℝ) + ((72419301 / 6250000000000000000)) * (126 / 100) + 2 * ((211681157 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13211) *
          (32 * (((81429369 / 5000000000000000000) : ℝ) + (72419301 / 6250000000000000000) + (211681157 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13211

/-! A coarse bound on the actual paper statistics constant at dimension 13212. -/
namespace BstLean.Part266.Row13212
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13210 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13210 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13210 128 ≤ (13464 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13464 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13212) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13212 : ℕ))
    (by norm_num : (13212 : ℕ) ≤ 16384)
  have ht : paperTail256 13212 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13212 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13212 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13212 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13212 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13212 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13210 128 * √(2 / (13212 : ℝ)) *
      (√(13212 : ℝ) + paperT0 13212 + paperTail256 13212) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13212 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13212 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13212 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13210 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13210 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13212 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13212

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13212
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13212 (61 / 100) 166 (17 / (100 * 13212)) (26 / (10 * 13212)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13212 (61 / 100) 166 (17 / (100 * 13212)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (26453911 / 6250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1281448929 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (29792409 / 8000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13212 / 13212 * (61 / 100)) ^ 4 * inverseRadius8 (13212 - 1) /
            envelopeGap 13212 (61 / 100) 166 (17 / (100 * 13212)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13212

namespace BstLean.Part266.Row13212
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13212 166 ≤ (4151518297 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13212 166 ≤ (27700333 / 20000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (332889267 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13212 166 ≤ (1628217753 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13212 166 ≤ (1158445797 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13212 166 ≤ (52908273 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (26453911 / 6250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (26453911 / 6250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1281448929 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (29792409 / 8000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((7006 / 1953125) : ℝ) ≤ √(17 / (100 * 13212) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13212) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1028667313 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (2237333207 / 62500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13212) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13212) ≤ (53520041 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13212) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13212 * (166 : ℝ) ^ 2 + 26 / (10 * 13212) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13212) : ℝ)) (tA 13212 * 166 ^ 2 + 26 / (10 * 13212)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((7006 / 1953125))) * ((26453911 / 6250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((7006 / 1953125)) ^ 3) * ((1281448929 / 1000000000000000000000000))) + ((29792409 / 8000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((7006 / 1953125)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13212) : ℝ)) d.D d.V d.P (√(tA 13212) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((7006 / 1953125)) ^ 2 * (((1028667313 / 500000000000000)) * ((2237333207 / 62500000000000000)))) + ((29792409 / 8000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13212) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((7006 / 1953125)) * ((26453911 / 6250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13212) : ℝ)) (tA 13212 * 166 ^ 2 + 26 / (10 * 13212)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((26453911 / 6250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((7006 / 1953125)) ^ 2) * ((1281448929 / 1000000000000000000000000)) + ((29792409 / 8000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13212) : ℝ)) (√(26 / (10 * 13212) : ℝ)) d.D d.V d.P (√(tA 13212) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((7006 / 1953125)) * (((1028667313 / 500000000000000)) * ((2237333207 / 62500000000000000))) + ((29792409 / 8000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13212) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((26453911 / 6250000000000000000) : ℝ) + ((29792409 / 8000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13212

namespace BstLean.Part266.Row13212
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13212 166 ∧
    0 ≤ (tableEnvelope C).f1 13212 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13212 166 ∧
    0 ≤ (tableEnvelope C).w1 13212 166 ∧ 0 ≤ (tableEnvelope C).w2 13212 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13212 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13212 166 ∧ 0 ≤ d.f1 13212 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13212 166 ∧ 0 ≤ d.w1 13212 166 ∧ 0 ≤ d.w2 13212 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13212 ≤ 2 * (228 / 100 : ℝ) / 13212 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13212 ≤ 2 * (370 / 100 : ℝ) / 13212 := by
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
    (completeRAData (tableEnvelope C) 13212 166).locationBound 13212 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13212 166).energyBound 13212 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13212 166) (d.f1 13212 166) d.f2 ≤
      32 * (((4151518297 / 1000000000000000000) : ℝ) + (27700333 / 20000000000000000) + (332889267 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13212 166) (d.w1 13212 166)
      (d.w2 13212 166) ≤
      32 * (((1628217753 / 100000000000000000000) : ℝ) + (1158445797 / 100000000000000000000) + (52908273 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13212 166) (d.f1 13212 166) d.f2 ≤
      ((4151518297 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4151518297 / 1000000000000000000)) * ((27700333 / 20000000000000000)) * (126 / 100) +
      2 * (((27700333 / 20000000000000000)) ^ 2 + 2 * ((4151518297 / 1000000000000000000)) * ((332889267 / 1000000000000000000))) +
      6 * ((27700333 / 20000000000000000)) * ((332889267 / 1000000000000000000)) * (126 / 100) + 8 * ((332889267 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13212 166) (d.f1 13212 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13212 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13212 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13212 166) (d.f1 13212 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13212 166) (d.w1 13212 166) (d.w2 13212 166)
  have hwexpr0 : 0 ≤ d.w0 13212 166 + d.w1 13212 166 * √(π / 2) +
      2 * d.w2 13212 166 + energyR16 13212 *
      radiusPolynomialRoot16 (d.w0 13212 166) (d.w1 13212 166) (d.w2 13212 166) := by
    positivity
  constructor
  · change (13212 : ℝ) ^ 8 * (mA 13212 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13212 166) (d.f1 13212 166) d.f2 + locationR16 13212 *
        radiusPolynomialRoot16 (d.f0 13212 166) (d.f1 13212 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13212 : ℝ) ^ 8 * (mA 13212 : ℝ) ^ 8 *
        ((((4151518297 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4151518297 / 1000000000000000000)) * ((27700333 / 20000000000000000)) * (126 / 100) +
          2 * (((27700333 / 20000000000000000)) ^ 2 + 2 * ((4151518297 / 1000000000000000000)) * ((332889267 / 1000000000000000000))) +
          6 * ((27700333 / 20000000000000000)) * ((332889267 / 1000000000000000000)) * (126 / 100) + 8 * ((332889267 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13212) *
          (32 * (((4151518297 / 1000000000000000000) : ℝ) + (27700333 / 20000000000000000) + (332889267 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13212 : ℝ) ^ 16 *
      (d.w0 13212 166 + d.w1 13212 166 * √(π / 2) + 2 * d.w2 13212 166 +
        energyR16 13212 * radiusPolynomialRoot16 (d.w0 13212 166) (d.w1 13212 166)
          (d.w2 13212 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13212 : ℝ) ^ 16 *
        (((1628217753 / 100000000000000000000) : ℝ) + ((1158445797 / 100000000000000000000)) * (126 / 100) + 2 * ((52908273 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13212) *
          (32 * (((1628217753 / 100000000000000000000) : ℝ) + (1158445797 / 100000000000000000000) + (52908273 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13212

/-! A coarse bound on the actual paper statistics constant at dimension 13213. -/
namespace BstLean.Part266.Row13213
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13211 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13211 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13211 128 ≤ (13465 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13465 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13213) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13213 : ℕ))
    (by norm_num : (13213 : ℕ) ≤ 16384)
  have ht : paperTail256 13213 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13213 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13213 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13213 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13213 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13213 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13211 128 * √(2 / (13213 : ℝ)) *
      (√(13213 : ℝ) + paperT0 13213 + paperTail256 13213) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13213 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13213 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13213 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13211 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13211 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13213 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13213

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13213
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13213 (61 / 100) 166 (17 / (100 * 13213)) (26 / (10 * 13213)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13213 (61 / 100) 166 (17 / (100 * 13213)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (423166477 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1281061023 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (372177591 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13213 / 13213 * (61 / 100)) ^ 4 * inverseRadius8 (13213 - 1) /
            envelopeGap 13213 (61 / 100) 166 (17 / (100 * 13213)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13213

namespace BstLean.Part266.Row13213
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13213 166 ≤ (518841707 / 125000000000000000)
  f1 : (tableEnvelope C).f1 13213 166 ≤ (1384754791 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (66565261 / 200000000000000000)
  w0 : (tableEnvelope C).w0 13213 166 ≤ (6511393 / 400000000000000000)
  w1 : (tableEnvelope C).w1 13213 166 ≤ (579091431 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13213 166 ≤ (423170083 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (423166477 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (423166477 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1281061023 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (372177591 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((448367 / 125000000) : ℝ) ≤ √(17 / (100 * 13213) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13213) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (102855053 / 50000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (2236994551 / 62500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13213) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13213) ≤ (107031981 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13213) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13213 * (166 : ℝ) ^ 2 + 26 / (10 * 13213) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13213) : ℝ)) (tA 13213 * 166 ^ 2 + 26 / (10 * 13213)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((448367 / 125000000))) * ((423166477 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((448367 / 125000000)) ^ 3) * ((1281061023 / 1000000000000000000000000))) + ((372177591 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((448367 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13213) : ℝ)) d.D d.V d.P (√(tA 13213) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((448367 / 125000000)) ^ 2 * (((102855053 / 50000000000000)) * ((2236994551 / 62500000000000000)))) + ((372177591 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13213) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((448367 / 125000000)) * ((423166477 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13213) : ℝ)) (tA 13213 * 166 ^ 2 + 26 / (10 * 13213)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((423166477 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((448367 / 125000000)) ^ 2) * ((1281061023 / 1000000000000000000000000)) + ((372177591 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13213) : ℝ)) (√(26 / (10 * 13213) : ℝ)) d.D d.V d.P (√(tA 13213) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((448367 / 125000000)) * (((102855053 / 50000000000000)) * ((2236994551 / 62500000000000000))) + ((372177591 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13213) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((423166477 / 100000000000000000000) : ℝ) + ((372177591 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13213

namespace BstLean.Part266.Row13213
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13213 166 ∧
    0 ≤ (tableEnvelope C).f1 13213 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13213 166 ∧
    0 ≤ (tableEnvelope C).w1 13213 166 ∧ 0 ≤ (tableEnvelope C).w2 13213 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13213 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13213 166 ∧ 0 ≤ d.f1 13213 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13213 166 ∧ 0 ≤ d.w1 13213 166 ∧ 0 ≤ d.w2 13213 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13213 ≤ 2 * (228 / 100 : ℝ) / 13213 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13213 ≤ 2 * (370 / 100 : ℝ) / 13213 := by
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
    (completeRAData (tableEnvelope C) 13213 166).locationBound 13213 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13213 166).energyBound 13213 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13213 166) (d.f1 13213 166) d.f2 ≤
      32 * (((518841707 / 125000000000000000) : ℝ) + (1384754791 / 1000000000000000000) + (66565261 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13213 166) (d.w1 13213 166)
      (d.w2 13213 166) ≤
      32 * (((6511393 / 400000000000000000) : ℝ) + (579091431 / 50000000000000000000) + (423170083 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13213 166) (d.f1 13213 166) d.f2 ≤
      ((518841707 / 125000000000000000) : ℝ) ^ 2 + 2 * ((518841707 / 125000000000000000)) * ((1384754791 / 1000000000000000000)) * (126 / 100) +
      2 * (((1384754791 / 1000000000000000000)) ^ 2 + 2 * ((518841707 / 125000000000000000)) * ((66565261 / 200000000000000000))) +
      6 * ((1384754791 / 1000000000000000000)) * ((66565261 / 200000000000000000)) * (126 / 100) + 8 * ((66565261 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13213 166) (d.f1 13213 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13213 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13213 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13213 166) (d.f1 13213 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13213 166) (d.w1 13213 166) (d.w2 13213 166)
  have hwexpr0 : 0 ≤ d.w0 13213 166 + d.w1 13213 166 * √(π / 2) +
      2 * d.w2 13213 166 + energyR16 13213 *
      radiusPolynomialRoot16 (d.w0 13213 166) (d.w1 13213 166) (d.w2 13213 166) := by
    positivity
  constructor
  · change (13213 : ℝ) ^ 8 * (mA 13213 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13213 166) (d.f1 13213 166) d.f2 + locationR16 13213 *
        radiusPolynomialRoot16 (d.f0 13213 166) (d.f1 13213 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13213 : ℝ) ^ 8 * (mA 13213 : ℝ) ^ 8 *
        ((((518841707 / 125000000000000000) : ℝ) ^ 2 + 2 * ((518841707 / 125000000000000000)) * ((1384754791 / 1000000000000000000)) * (126 / 100) +
          2 * (((1384754791 / 1000000000000000000)) ^ 2 + 2 * ((518841707 / 125000000000000000)) * ((66565261 / 200000000000000000))) +
          6 * ((1384754791 / 1000000000000000000)) * ((66565261 / 200000000000000000)) * (126 / 100) + 8 * ((66565261 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13213) *
          (32 * (((518841707 / 125000000000000000) : ℝ) + (1384754791 / 1000000000000000000) + (66565261 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13213 : ℝ) ^ 16 *
      (d.w0 13213 166 + d.w1 13213 166 * √(π / 2) + 2 * d.w2 13213 166 +
        energyR16 13213 * radiusPolynomialRoot16 (d.w0 13213 166) (d.w1 13213 166)
          (d.w2 13213 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13213 : ℝ) ^ 16 *
        (((6511393 / 400000000000000000) : ℝ) + ((579091431 / 50000000000000000000)) * (126 / 100) + 2 * ((423170083 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13213) *
          (32 * (((6511393 / 400000000000000000) : ℝ) + (579091431 / 50000000000000000000) + (423170083 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13213

/-! A coarse bound on the actual paper statistics constant at dimension 13214. -/
namespace BstLean.Part266.Row13214
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13212 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13212 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13212 128 ≤ (13466 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13466 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13214) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13214 : ℕ))
    (by norm_num : (13214 : ℕ) ≤ 16384)
  have ht : paperTail256 13214 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13214 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13214 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13214 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13214 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13214 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13212 128 * √(2 / (13214 : ℝ)) *
      (√(13214 : ℝ) + paperT0 13214 + paperTail256 13214) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13214 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13214 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13214 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13212 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13212 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13214 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13214

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13214
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13214 (61 / 100) 166 (17 / (100 * 13214)) (26 / (10 * 13214)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13214 (61 / 100) 166 (17 / (100 * 13214)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (423070407 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1280673263 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (185975113 / 50000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13214 / 13214 * (61 / 100)) ^ 4 * inverseRadius8 (13214 - 1) /
            envelopeGap 13214 (61 / 100) 166 (17 / (100 * 13214)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13214

namespace BstLean.Part266.Row13214
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13214 166 ≤ (4149945931 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13214 166 ≤ (692246121 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (332763269 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13214 166 ≤ (1627478197 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13214 166 ≤ (1157919689 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13214 166 ≤ (423074011 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (423070407 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (423070407 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1280673263 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (185975113 / 50000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3586801 / 1000000000) : ℝ) ≤ √(17 / (100 * 13214) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13214) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2056867539 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1789324777 / 50000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13214) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13214) ≤ (107023881 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13214) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13214 * (166 : ℝ) ^ 2 + 26 / (10 * 13214) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13214) : ℝ)) (tA 13214 * 166 ^ 2 + 26 / (10 * 13214)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3586801 / 1000000000))) * ((423070407 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3586801 / 1000000000)) ^ 3) * ((1280673263 / 1000000000000000000000000))) + ((185975113 / 50000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3586801 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13214) : ℝ)) d.D d.V d.P (√(tA 13214) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3586801 / 1000000000)) ^ 2 * (((2056867539 / 1000000000000000)) * ((1789324777 / 50000000000000000)))) + ((185975113 / 50000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13214) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3586801 / 1000000000)) * ((423070407 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13214) : ℝ)) (tA 13214 * 166 ^ 2 + 26 / (10 * 13214)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((423070407 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3586801 / 1000000000)) ^ 2) * ((1280673263 / 1000000000000000000000000)) + ((185975113 / 50000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13214) : ℝ)) (√(26 / (10 * 13214) : ℝ)) d.D d.V d.P (√(tA 13214) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3586801 / 1000000000)) * (((2056867539 / 1000000000000000)) * ((1789324777 / 50000000000000000))) + ((185975113 / 50000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13214) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((423070407 / 100000000000000000000) : ℝ) + ((185975113 / 50000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13214

namespace BstLean.Part266.Row13214
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13214 166 ∧
    0 ≤ (tableEnvelope C).f1 13214 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13214 166 ∧
    0 ≤ (tableEnvelope C).w1 13214 166 ∧ 0 ≤ (tableEnvelope C).w2 13214 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13214 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13214 166 ∧ 0 ≤ d.f1 13214 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13214 166 ∧ 0 ≤ d.w1 13214 166 ∧ 0 ≤ d.w2 13214 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13214 ≤ 2 * (228 / 100 : ℝ) / 13214 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13214 ≤ 2 * (370 / 100 : ℝ) / 13214 := by
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
    (completeRAData (tableEnvelope C) 13214 166).locationBound 13214 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13214 166).energyBound 13214 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13214 166) (d.f1 13214 166) d.f2 ≤
      32 * (((4149945931 / 1000000000000000000) : ℝ) + (692246121 / 500000000000000000) + (332763269 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13214 166) (d.w1 13214 166)
      (d.w2 13214 166) ≤
      32 * (((1627478197 / 100000000000000000000) : ℝ) + (1157919689 / 100000000000000000000) + (423074011 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13214 166) (d.f1 13214 166) d.f2 ≤
      ((4149945931 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4149945931 / 1000000000000000000)) * ((692246121 / 500000000000000000)) * (126 / 100) +
      2 * (((692246121 / 500000000000000000)) ^ 2 + 2 * ((4149945931 / 1000000000000000000)) * ((332763269 / 1000000000000000000))) +
      6 * ((692246121 / 500000000000000000)) * ((332763269 / 1000000000000000000)) * (126 / 100) + 8 * ((332763269 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13214 166) (d.f1 13214 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13214 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13214 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13214 166) (d.f1 13214 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13214 166) (d.w1 13214 166) (d.w2 13214 166)
  have hwexpr0 : 0 ≤ d.w0 13214 166 + d.w1 13214 166 * √(π / 2) +
      2 * d.w2 13214 166 + energyR16 13214 *
      radiusPolynomialRoot16 (d.w0 13214 166) (d.w1 13214 166) (d.w2 13214 166) := by
    positivity
  constructor
  · change (13214 : ℝ) ^ 8 * (mA 13214 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13214 166) (d.f1 13214 166) d.f2 + locationR16 13214 *
        radiusPolynomialRoot16 (d.f0 13214 166) (d.f1 13214 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13214 : ℝ) ^ 8 * (mA 13214 : ℝ) ^ 8 *
        ((((4149945931 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4149945931 / 1000000000000000000)) * ((692246121 / 500000000000000000)) * (126 / 100) +
          2 * (((692246121 / 500000000000000000)) ^ 2 + 2 * ((4149945931 / 1000000000000000000)) * ((332763269 / 1000000000000000000))) +
          6 * ((692246121 / 500000000000000000)) * ((332763269 / 1000000000000000000)) * (126 / 100) + 8 * ((332763269 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13214) *
          (32 * (((4149945931 / 1000000000000000000) : ℝ) + (692246121 / 500000000000000000) + (332763269 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13214 : ℝ) ^ 16 *
      (d.w0 13214 166 + d.w1 13214 166 * √(π / 2) + 2 * d.w2 13214 166 +
        energyR16 13214 * radiusPolynomialRoot16 (d.w0 13214 166) (d.w1 13214 166)
          (d.w2 13214 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13214 : ℝ) ^ 16 *
        (((1627478197 / 100000000000000000000) : ℝ) + ((1157919689 / 100000000000000000000)) * (126 / 100) + 2 * ((423074011 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13214) *
          (32 * (((1627478197 / 100000000000000000000) : ℝ) + (1157919689 / 100000000000000000000) + (423074011 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13214

/-! A coarse bound on the actual paper statistics constant at dimension 13215. -/
namespace BstLean.Part266.Row13215
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13213 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13213 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13213 128 ≤ (13467 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13467 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13215) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13215 : ℕ))
    (by norm_num : (13215 : ℕ) ≤ 16384)
  have ht : paperTail256 13215 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13215 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13215 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13215 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13215 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13215 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13213 128 * √(2 / (13215 : ℝ)) *
      (√(13215 : ℝ) + paperT0 13215 + paperTail256 13215) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13215 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13215 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13215 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13213 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13213 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13215 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13215

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13215
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13215 (61 / 100) 166 (17 / (100 * 13215)) (26 / (10 * 13215)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13215 (61 / 100) 166 (17 / (100 * 13215)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (211487183 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (25605713 / 20000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (148689207 / 40000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13215 / 13215 * (61 / 100)) ^ 4 * inverseRadius8 (13215 - 1) /
            envelopeGap 13215 (61 / 100) 166 (17 / (100 * 13215)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13215

namespace BstLean.Part266.Row13215
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13215 166 ≤ (4149161807 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13215 166 ≤ (692115273 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (332700343 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13215 166 ≤ (1627108937 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13215 166 ≤ (1157656923 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13215 166 ≤ (422977967 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (211487183 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (211487183 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (25605713 / 20000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (148689207 / 40000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((717333 / 200000000) : ℝ) ≤ √(17 / (100 * 13215) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13215) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2056634061 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (17890539749 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13215) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13215) ≤ (107015783 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13215) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13215 * (166 : ℝ) ^ 2 + 26 / (10 * 13215) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13215) : ℝ)) (tA 13215 * 166 ^ 2 + 26 / (10 * 13215)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((717333 / 200000000))) * ((211487183 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((717333 / 200000000)) ^ 3) * ((25605713 / 20000000000000000000000))) + ((148689207 / 40000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((717333 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13215) : ℝ)) d.D d.V d.P (√(tA 13215) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((717333 / 200000000)) ^ 2 * (((2056634061 / 1000000000000000)) * ((17890539749 / 500000000000000000)))) + ((148689207 / 40000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13215) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((717333 / 200000000)) * ((211487183 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13215) : ℝ)) (tA 13215 * 166 ^ 2 + 26 / (10 * 13215)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((211487183 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((717333 / 200000000)) ^ 2) * ((25605713 / 20000000000000000000000)) + ((148689207 / 40000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13215) : ℝ)) (√(26 / (10 * 13215) : ℝ)) d.D d.V d.P (√(tA 13215) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((717333 / 200000000)) * (((2056634061 / 1000000000000000)) * ((17890539749 / 500000000000000000))) + ((148689207 / 40000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13215) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((211487183 / 50000000000000000000) : ℝ) + ((148689207 / 40000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13215

namespace BstLean.Part266.Row13215
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13215 166 ∧
    0 ≤ (tableEnvelope C).f1 13215 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13215 166 ∧
    0 ≤ (tableEnvelope C).w1 13215 166 ∧ 0 ≤ (tableEnvelope C).w2 13215 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13215 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13215 166 ∧ 0 ≤ d.f1 13215 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13215 166 ∧ 0 ≤ d.w1 13215 166 ∧ 0 ≤ d.w2 13215 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13215 ≤ 2 * (228 / 100 : ℝ) / 13215 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13215 ≤ 2 * (370 / 100 : ℝ) / 13215 := by
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
    (completeRAData (tableEnvelope C) 13215 166).locationBound 13215 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13215 166).energyBound 13215 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13215 166) (d.f1 13215 166) d.f2 ≤
      32 * (((4149161807 / 1000000000000000000) : ℝ) + (692115273 / 500000000000000000) + (332700343 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13215 166) (d.w1 13215 166)
      (d.w2 13215 166) ≤
      32 * (((1627108937 / 100000000000000000000) : ℝ) + (1157656923 / 100000000000000000000) + (422977967 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13215 166) (d.f1 13215 166) d.f2 ≤
      ((4149161807 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4149161807 / 1000000000000000000)) * ((692115273 / 500000000000000000)) * (126 / 100) +
      2 * (((692115273 / 500000000000000000)) ^ 2 + 2 * ((4149161807 / 1000000000000000000)) * ((332700343 / 1000000000000000000))) +
      6 * ((692115273 / 500000000000000000)) * ((332700343 / 1000000000000000000)) * (126 / 100) + 8 * ((332700343 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13215 166) (d.f1 13215 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13215 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13215 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13215 166) (d.f1 13215 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13215 166) (d.w1 13215 166) (d.w2 13215 166)
  have hwexpr0 : 0 ≤ d.w0 13215 166 + d.w1 13215 166 * √(π / 2) +
      2 * d.w2 13215 166 + energyR16 13215 *
      radiusPolynomialRoot16 (d.w0 13215 166) (d.w1 13215 166) (d.w2 13215 166) := by
    positivity
  constructor
  · change (13215 : ℝ) ^ 8 * (mA 13215 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13215 166) (d.f1 13215 166) d.f2 + locationR16 13215 *
        radiusPolynomialRoot16 (d.f0 13215 166) (d.f1 13215 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13215 : ℝ) ^ 8 * (mA 13215 : ℝ) ^ 8 *
        ((((4149161807 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4149161807 / 1000000000000000000)) * ((692115273 / 500000000000000000)) * (126 / 100) +
          2 * (((692115273 / 500000000000000000)) ^ 2 + 2 * ((4149161807 / 1000000000000000000)) * ((332700343 / 1000000000000000000))) +
          6 * ((692115273 / 500000000000000000)) * ((332700343 / 1000000000000000000)) * (126 / 100) + 8 * ((332700343 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13215) *
          (32 * (((4149161807 / 1000000000000000000) : ℝ) + (692115273 / 500000000000000000) + (332700343 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13215 : ℝ) ^ 16 *
      (d.w0 13215 166 + d.w1 13215 166 * √(π / 2) + 2 * d.w2 13215 166 +
        energyR16 13215 * radiusPolynomialRoot16 (d.w0 13215 166) (d.w1 13215 166)
          (d.w2 13215 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13215 : ℝ) ^ 16 *
        (((1627108937 / 100000000000000000000) : ℝ) + ((1157656923 / 100000000000000000000)) * (126 / 100) + 2 * ((422977967 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13215) *
          (32 * (((1627108937 / 100000000000000000000) : ℝ) + (1157656923 / 100000000000000000000) + (422977967 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13215

/-! A coarse bound on the actual paper statistics constant at dimension 13216. -/
namespace BstLean.Part266.Row13216
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13214 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13214 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13214 128 ≤ (13468 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13468 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13216) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13216 : ℕ))
    (by norm_num : (13216 : ℕ) ≤ 16384)
  have ht : paperTail256 13216 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13216 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13216 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13216 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13216 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13216 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13214 128 * √(2 / (13216 : ℝ)) *
      (√(13216 : ℝ) + paperT0 13216 + paperTail256 13216) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13216 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13216 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13216 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13214 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13214 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13216 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13216

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13216
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13216 (61 / 100) 166 (17 / (100 * 13216)) (26 / (10 * 13216)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13216 (61 / 100) 166 (17 / (100 * 13216)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (211439177 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (159987273 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (928739913 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13216 / 13216 * (61 / 100)) ^ 4 * inverseRadius8 (13216 - 1) /
            envelopeGap 13216 (61 / 100) 166 (17 / (100 * 13216)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13216

namespace BstLean.Part266.Row13216
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13216 166 ≤ (4148377943 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13216 166 ≤ (345992233 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (83159359 / 250000000000000000)
  w0 : (tableEnvelope C).w0 13216 166 ≤ (8133699 / 500000000000000000)
  w1 : (tableEnvelope C).w1 13216 166 ≤ (578697121 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13216 166 ≤ (422881953 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (211439177 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (211439177 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (159987273 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (928739913 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3586529 / 1000000000) : ℝ) ≤ √(17 / (100 * 13216) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13216) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (514100157 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3577566469 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13216) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13216) ≤ (21401537 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13216) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13216 * (166 : ℝ) ^ 2 + 26 / (10 * 13216) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13216) : ℝ)) (tA 13216 * 166 ^ 2 + 26 / (10 * 13216)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3586529 / 1000000000))) * ((211439177 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3586529 / 1000000000)) ^ 3) * ((159987273 / 125000000000000000000000))) + ((928739913 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3586529 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13216) : ℝ)) d.D d.V d.P (√(tA 13216) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3586529 / 1000000000)) ^ 2 * (((514100157 / 250000000000000)) * ((3577566469 / 100000000000000000)))) + ((928739913 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13216) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3586529 / 1000000000)) * ((211439177 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13216) : ℝ)) (tA 13216 * 166 ^ 2 + 26 / (10 * 13216)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((211439177 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3586529 / 1000000000)) ^ 2) * ((159987273 / 125000000000000000000000)) + ((928739913 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13216) : ℝ)) (√(26 / (10 * 13216) : ℝ)) d.D d.V d.P (√(tA 13216) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3586529 / 1000000000)) * (((514100157 / 250000000000000)) * ((3577566469 / 100000000000000000))) + ((928739913 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13216) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((211439177 / 50000000000000000000) : ℝ) + ((928739913 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13216

namespace BstLean.Part266.Row13216
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13216 166 ∧
    0 ≤ (tableEnvelope C).f1 13216 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13216 166 ∧
    0 ≤ (tableEnvelope C).w1 13216 166 ∧ 0 ≤ (tableEnvelope C).w2 13216 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13216 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13216 166 ∧ 0 ≤ d.f1 13216 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13216 166 ∧ 0 ≤ d.w1 13216 166 ∧ 0 ≤ d.w2 13216 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13216 ≤ 2 * (228 / 100 : ℝ) / 13216 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13216 ≤ 2 * (370 / 100 : ℝ) / 13216 := by
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
    (completeRAData (tableEnvelope C) 13216 166).locationBound 13216 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13216 166).energyBound 13216 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13216 166) (d.f1 13216 166) d.f2 ≤
      32 * (((4148377943 / 1000000000000000000) : ℝ) + (345992233 / 250000000000000000) + (83159359 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13216 166) (d.w1 13216 166)
      (d.w2 13216 166) ≤
      32 * (((8133699 / 500000000000000000) : ℝ) + (578697121 / 50000000000000000000) + (422881953 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13216 166) (d.f1 13216 166) d.f2 ≤
      ((4148377943 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4148377943 / 1000000000000000000)) * ((345992233 / 250000000000000000)) * (126 / 100) +
      2 * (((345992233 / 250000000000000000)) ^ 2 + 2 * ((4148377943 / 1000000000000000000)) * ((83159359 / 250000000000000000))) +
      6 * ((345992233 / 250000000000000000)) * ((83159359 / 250000000000000000)) * (126 / 100) + 8 * ((83159359 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13216 166) (d.f1 13216 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13216 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13216 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13216 166) (d.f1 13216 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13216 166) (d.w1 13216 166) (d.w2 13216 166)
  have hwexpr0 : 0 ≤ d.w0 13216 166 + d.w1 13216 166 * √(π / 2) +
      2 * d.w2 13216 166 + energyR16 13216 *
      radiusPolynomialRoot16 (d.w0 13216 166) (d.w1 13216 166) (d.w2 13216 166) := by
    positivity
  constructor
  · change (13216 : ℝ) ^ 8 * (mA 13216 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13216 166) (d.f1 13216 166) d.f2 + locationR16 13216 *
        radiusPolynomialRoot16 (d.f0 13216 166) (d.f1 13216 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13216 : ℝ) ^ 8 * (mA 13216 : ℝ) ^ 8 *
        ((((4148377943 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4148377943 / 1000000000000000000)) * ((345992233 / 250000000000000000)) * (126 / 100) +
          2 * (((345992233 / 250000000000000000)) ^ 2 + 2 * ((4148377943 / 1000000000000000000)) * ((83159359 / 250000000000000000))) +
          6 * ((345992233 / 250000000000000000)) * ((83159359 / 250000000000000000)) * (126 / 100) + 8 * ((83159359 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13216) *
          (32 * (((4148377943 / 1000000000000000000) : ℝ) + (345992233 / 250000000000000000) + (83159359 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13216 : ℝ) ^ 16 *
      (d.w0 13216 166 + d.w1 13216 166 * √(π / 2) + 2 * d.w2 13216 166 +
        energyR16 13216 * radiusPolynomialRoot16 (d.w0 13216 166) (d.w1 13216 166)
          (d.w2 13216 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13216 : ℝ) ^ 16 *
        (((8133699 / 500000000000000000) : ℝ) + ((578697121 / 50000000000000000000)) * (126 / 100) + 2 * ((422881953 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13216) *
          (32 * (((8133699 / 500000000000000000) : ℝ) + (578697121 / 50000000000000000000) + (422881953 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13216

/-! A coarse bound on the actual paper statistics constant at dimension 13217. -/
namespace BstLean.Part266.Row13217
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13215 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13215 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13215 128 ≤ (13469 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13469 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13217) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13217 : ℕ))
    (by norm_num : (13217 : ℕ) ≤ 16384)
  have ht : paperTail256 13217 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13217 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13217 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13217 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13217 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13217 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13215 128 * √(2 / (13217 : ℝ)) *
      (√(13217 : ℝ) + paperT0 13217 + paperTail256 13217) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13217 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13217 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13217 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13215 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13215 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13217 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13217

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13217
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13217 (61 / 100) 166 (17 / (100 * 13217)) (26 / (10 * 13217)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13217 (61 / 100) 166 (17 / (100 * 13217)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (105695593 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (79969429 / 62500000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3712690691 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13217 / 13217 * (61 / 100)) ^ 4 * inverseRadius8 (13217 - 1) /
            envelopeGap 13217 (61 / 100) 166 (17 / (100 * 13217)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13217

namespace BstLean.Part266.Row13217
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13217 166 ≤ (4147590999 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13217 166 ≤ (345926657 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (66514891 / 200000000000000000)
  w0 : (tableEnvelope C).w0 13217 166 ≤ (813185057 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13217 166 ≤ (289282831 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 13217 166 ≤ (422785969 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (105695593 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (105695593 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (79969429 / 62500000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3712690691 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1793197 / 500000000) : ℝ) ≤ √(17 / (100 * 13217) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13217) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2056167241 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1117820347 / 31250000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13217) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13217) ≤ (106999589 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13217) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13217 * (166 : ℝ) ^ 2 + 26 / (10 * 13217) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13217) : ℝ)) (tA 13217 * 166 ^ 2 + 26 / (10 * 13217)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1793197 / 500000000))) * ((105695593 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1793197 / 500000000)) ^ 3) * ((79969429 / 62500000000000000000000))) + ((3712690691 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1793197 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13217) : ℝ)) d.D d.V d.P (√(tA 13217) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1793197 / 500000000)) ^ 2 * (((2056167241 / 1000000000000000)) * ((1117820347 / 31250000000000000)))) + ((3712690691 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13217) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1793197 / 500000000)) * ((105695593 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13217) : ℝ)) (tA 13217 * 166 ^ 2 + 26 / (10 * 13217)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((105695593 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1793197 / 500000000)) ^ 2) * ((79969429 / 62500000000000000000000)) + ((3712690691 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13217) : ℝ)) (√(26 / (10 * 13217) : ℝ)) d.D d.V d.P (√(tA 13217) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1793197 / 500000000)) * (((2056167241 / 1000000000000000)) * ((1117820347 / 31250000000000000))) + ((3712690691 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13217) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((105695593 / 25000000000000000000) : ℝ) + ((3712690691 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13217

namespace BstLean.Part266.Row13217
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13217 166 ∧
    0 ≤ (tableEnvelope C).f1 13217 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13217 166 ∧
    0 ≤ (tableEnvelope C).w1 13217 166 ∧ 0 ≤ (tableEnvelope C).w2 13217 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13217 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13217 166 ∧ 0 ≤ d.f1 13217 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13217 166 ∧ 0 ≤ d.w1 13217 166 ∧ 0 ≤ d.w2 13217 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13217 ≤ 2 * (228 / 100 : ℝ) / 13217 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13217 ≤ 2 * (370 / 100 : ℝ) / 13217 := by
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
    (completeRAData (tableEnvelope C) 13217 166).locationBound 13217 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13217 166).energyBound 13217 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13217 166) (d.f1 13217 166) d.f2 ≤
      32 * (((4147590999 / 1000000000000000000) : ℝ) + (345926657 / 250000000000000000) + (66514891 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13217 166) (d.w1 13217 166)
      (d.w2 13217 166) ≤
      32 * (((813185057 / 50000000000000000000) : ℝ) + (289282831 / 25000000000000000000) + (422785969 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13217 166) (d.f1 13217 166) d.f2 ≤
      ((4147590999 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4147590999 / 1000000000000000000)) * ((345926657 / 250000000000000000)) * (126 / 100) +
      2 * (((345926657 / 250000000000000000)) ^ 2 + 2 * ((4147590999 / 1000000000000000000)) * ((66514891 / 200000000000000000))) +
      6 * ((345926657 / 250000000000000000)) * ((66514891 / 200000000000000000)) * (126 / 100) + 8 * ((66514891 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13217 166) (d.f1 13217 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13217 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13217 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13217 166) (d.f1 13217 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13217 166) (d.w1 13217 166) (d.w2 13217 166)
  have hwexpr0 : 0 ≤ d.w0 13217 166 + d.w1 13217 166 * √(π / 2) +
      2 * d.w2 13217 166 + energyR16 13217 *
      radiusPolynomialRoot16 (d.w0 13217 166) (d.w1 13217 166) (d.w2 13217 166) := by
    positivity
  constructor
  · change (13217 : ℝ) ^ 8 * (mA 13217 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13217 166) (d.f1 13217 166) d.f2 + locationR16 13217 *
        radiusPolynomialRoot16 (d.f0 13217 166) (d.f1 13217 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13217 : ℝ) ^ 8 * (mA 13217 : ℝ) ^ 8 *
        ((((4147590999 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4147590999 / 1000000000000000000)) * ((345926657 / 250000000000000000)) * (126 / 100) +
          2 * (((345926657 / 250000000000000000)) ^ 2 + 2 * ((4147590999 / 1000000000000000000)) * ((66514891 / 200000000000000000))) +
          6 * ((345926657 / 250000000000000000)) * ((66514891 / 200000000000000000)) * (126 / 100) + 8 * ((66514891 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13217) *
          (32 * (((4147590999 / 1000000000000000000) : ℝ) + (345926657 / 250000000000000000) + (66514891 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13217 : ℝ) ^ 16 *
      (d.w0 13217 166 + d.w1 13217 166 * √(π / 2) + 2 * d.w2 13217 166 +
        energyR16 13217 * radiusPolynomialRoot16 (d.w0 13217 166) (d.w1 13217 166)
          (d.w2 13217 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13217 : ℝ) ^ 16 *
        (((813185057 / 50000000000000000000) : ℝ) + ((289282831 / 25000000000000000000)) * (126 / 100) + 2 * ((422785969 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13217) *
          (32 * (((813185057 / 50000000000000000000) : ℝ) + (289282831 / 25000000000000000000) + (422785969 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13217

/-! A coarse bound on the actual paper statistics constant at dimension 13218. -/
namespace BstLean.Part266.Row13218
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13216 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13216 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13216 128 ≤ (13470 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13470 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13218) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13218 : ℕ))
    (by norm_num : (13218 : ℕ) ≤ 16384)
  have ht : paperTail256 13218 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13218 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13218 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13218 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13218 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13218 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13216 128 * √(2 / (13218 : ℝ)) *
      (√(13218 : ℝ) + paperT0 13218 + paperTail256 13218) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13218 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13218 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13218 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13216 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13216 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13218 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13218

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13218
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13218 (61 / 100) 166 (17 / (100 * 13218)) (26 / (10 * 13218)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13218 (61 / 100) 166 (17 / (100 * 13218)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (211343209 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1279123691 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3710423291 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13218 / 13218 * (61 / 100)) ^ 4 * inverseRadius8 (13218 - 1) /
            envelopeGap 13218 (61 / 100) 166 (17 / (100 * 13218)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13218

namespace BstLean.Part266.Row13218
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13218 166 ≤ (4146807653 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13218 166 ≤ (55337807 / 40000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (332511583 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13218 166 ≤ (1626001221 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13218 166 ≤ (1156868811 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13218 166 ≤ (422690013 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (211343209 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (211343209 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1279123691 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3710423291 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1793129 / 500000000) : ℝ) ≤ √(17 / (100 * 13218) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13218) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (411186779 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (35764838753 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13218) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13218) ≤ (53495747 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13218) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13218 * (166 : ℝ) ^ 2 + 26 / (10 * 13218) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13218) : ℝ)) (tA 13218 * 166 ^ 2 + 26 / (10 * 13218)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1793129 / 500000000))) * ((211343209 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1793129 / 500000000)) ^ 3) * ((1279123691 / 1000000000000000000000000))) + ((3710423291 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1793129 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13218) : ℝ)) d.D d.V d.P (√(tA 13218) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1793129 / 500000000)) ^ 2 * (((411186779 / 200000000000000)) * ((35764838753 / 1000000000000000000)))) + ((3710423291 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13218) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1793129 / 500000000)) * ((211343209 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13218) : ℝ)) (tA 13218 * 166 ^ 2 + 26 / (10 * 13218)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((211343209 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1793129 / 500000000)) ^ 2) * ((1279123691 / 1000000000000000000000000)) + ((3710423291 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13218) : ℝ)) (√(26 / (10 * 13218) : ℝ)) d.D d.V d.P (√(tA 13218) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1793129 / 500000000)) * (((411186779 / 200000000000000)) * ((35764838753 / 1000000000000000000))) + ((3710423291 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13218) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((211343209 / 50000000000000000000) : ℝ) + ((3710423291 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13218

namespace BstLean.Part266.Row13218
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13218 166 ∧
    0 ≤ (tableEnvelope C).f1 13218 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13218 166 ∧
    0 ≤ (tableEnvelope C).w1 13218 166 ∧ 0 ≤ (tableEnvelope C).w2 13218 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13218 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13218 166 ∧ 0 ≤ d.f1 13218 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13218 166 ∧ 0 ≤ d.w1 13218 166 ∧ 0 ≤ d.w2 13218 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13218 ≤ 2 * (228 / 100 : ℝ) / 13218 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13218 ≤ 2 * (370 / 100 : ℝ) / 13218 := by
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
    (completeRAData (tableEnvelope C) 13218 166).locationBound 13218 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13218 166).energyBound 13218 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13218 166) (d.f1 13218 166) d.f2 ≤
      32 * (((4146807653 / 1000000000000000000) : ℝ) + (55337807 / 40000000000000000) + (332511583 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13218 166) (d.w1 13218 166)
      (d.w2 13218 166) ≤
      32 * (((1626001221 / 100000000000000000000) : ℝ) + (1156868811 / 100000000000000000000) + (422690013 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13218 166) (d.f1 13218 166) d.f2 ≤
      ((4146807653 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4146807653 / 1000000000000000000)) * ((55337807 / 40000000000000000)) * (126 / 100) +
      2 * (((55337807 / 40000000000000000)) ^ 2 + 2 * ((4146807653 / 1000000000000000000)) * ((332511583 / 1000000000000000000))) +
      6 * ((55337807 / 40000000000000000)) * ((332511583 / 1000000000000000000)) * (126 / 100) + 8 * ((332511583 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13218 166) (d.f1 13218 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13218 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13218 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13218 166) (d.f1 13218 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13218 166) (d.w1 13218 166) (d.w2 13218 166)
  have hwexpr0 : 0 ≤ d.w0 13218 166 + d.w1 13218 166 * √(π / 2) +
      2 * d.w2 13218 166 + energyR16 13218 *
      radiusPolynomialRoot16 (d.w0 13218 166) (d.w1 13218 166) (d.w2 13218 166) := by
    positivity
  constructor
  · change (13218 : ℝ) ^ 8 * (mA 13218 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13218 166) (d.f1 13218 166) d.f2 + locationR16 13218 *
        radiusPolynomialRoot16 (d.f0 13218 166) (d.f1 13218 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13218 : ℝ) ^ 8 * (mA 13218 : ℝ) ^ 8 *
        ((((4146807653 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4146807653 / 1000000000000000000)) * ((55337807 / 40000000000000000)) * (126 / 100) +
          2 * (((55337807 / 40000000000000000)) ^ 2 + 2 * ((4146807653 / 1000000000000000000)) * ((332511583 / 1000000000000000000))) +
          6 * ((55337807 / 40000000000000000)) * ((332511583 / 1000000000000000000)) * (126 / 100) + 8 * ((332511583 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13218) *
          (32 * (((4146807653 / 1000000000000000000) : ℝ) + (55337807 / 40000000000000000) + (332511583 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13218 : ℝ) ^ 16 *
      (d.w0 13218 166 + d.w1 13218 166 * √(π / 2) + 2 * d.w2 13218 166 +
        energyR16 13218 * radiusPolynomialRoot16 (d.w0 13218 166) (d.w1 13218 166)
          (d.w2 13218 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13218 : ℝ) ^ 16 *
        (((1626001221 / 100000000000000000000) : ℝ) + ((1156868811 / 100000000000000000000)) * (126 / 100) + 2 * ((422690013 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13218) *
          (32 * (((1626001221 / 100000000000000000000) : ℝ) + (1156868811 / 100000000000000000000) + (422690013 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13218

/-! A coarse bound on the actual paper statistics constant at dimension 13219. -/
namespace BstLean.Part266.Row13219
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13217 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13217 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13217 128 ≤ (13471 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13471 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13219) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13219 : ℕ))
    (by norm_num : (13219 : ℕ) ≤ 16384)
  have ht : paperTail256 13219 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13219 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13219 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13219 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13219 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13219 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13217 128 * √(2 / (13219 : ℝ)) *
      (√(13219 : ℝ) + paperT0 13219 + paperTail256 13219) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13219 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13219 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13219 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13217 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13217 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13219 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13219

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13219
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13219 (61 / 100) 166 (17 / (100 * 13219)) (26 / (10 * 13219)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13219 (61 / 100) 166 (17 / (100 * 13219)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (422590493 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (159842083 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (74163149 / 20000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13219 / 13219 * (61 / 100)) ^ 4 * inverseRadius8 (13219 - 1) /
            envelopeGap 13219 (61 / 100) 166 (17 / (100 * 13219)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13219

namespace BstLean.Part266.Row13219
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13219 166 ≤ (1036506141 / 250000000000000000)
  f1 : (tableEnvelope C).f1 13219 166 ≤ (1383183803 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (33244873 / 100000000000000000)
  w0 : (tableEnvelope C).w0 13219 166 ≤ (32512649 / 2000000000000000000)
  w1 : (tableEnvelope C).w1 13219 166 ≤ (1156606383 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13219 166 ≤ (211297043 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (422590493 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (422590493 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (159842083 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (74163149 / 20000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1793061 / 500000000) : ℝ) ≤ √(17 / (100 * 13219) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13219) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1027850297 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (286075421 / 8000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13219) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13219) ≤ (534917 / 5000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13219) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13219 * (166 : ℝ) ^ 2 + 26 / (10 * 13219) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13219) : ℝ)) (tA 13219 * 166 ^ 2 + 26 / (10 * 13219)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1793061 / 500000000))) * ((422590493 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1793061 / 500000000)) ^ 3) * ((159842083 / 125000000000000000000000))) + ((74163149 / 20000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1793061 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13219) : ℝ)) d.D d.V d.P (√(tA 13219) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1793061 / 500000000)) ^ 2 * (((1027850297 / 500000000000000)) * ((286075421 / 8000000000000000)))) + ((74163149 / 20000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13219) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1793061 / 500000000)) * ((422590493 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13219) : ℝ)) (tA 13219 * 166 ^ 2 + 26 / (10 * 13219)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((422590493 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1793061 / 500000000)) ^ 2) * ((159842083 / 125000000000000000000000)) + ((74163149 / 20000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13219) : ℝ)) (√(26 / (10 * 13219) : ℝ)) d.D d.V d.P (√(tA 13219) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1793061 / 500000000)) * (((1027850297 / 500000000000000)) * ((286075421 / 8000000000000000))) + ((74163149 / 20000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13219) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((422590493 / 100000000000000000000) : ℝ) + ((74163149 / 20000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13219

namespace BstLean.Part266.Row13219
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13219 166 ∧
    0 ≤ (tableEnvelope C).f1 13219 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13219 166 ∧
    0 ≤ (tableEnvelope C).w1 13219 166 ∧ 0 ≤ (tableEnvelope C).w2 13219 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13219 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13219 166 ∧ 0 ≤ d.f1 13219 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13219 166 ∧ 0 ≤ d.w1 13219 166 ∧ 0 ≤ d.w2 13219 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13219 ≤ 2 * (228 / 100 : ℝ) / 13219 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13219 ≤ 2 * (370 / 100 : ℝ) / 13219 := by
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
    (completeRAData (tableEnvelope C) 13219 166).locationBound 13219 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13219 166).energyBound 13219 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13219 166) (d.f1 13219 166) d.f2 ≤
      32 * (((1036506141 / 250000000000000000) : ℝ) + (1383183803 / 1000000000000000000) + (33244873 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13219 166) (d.w1 13219 166)
      (d.w2 13219 166) ≤
      32 * (((32512649 / 2000000000000000000) : ℝ) + (1156606383 / 100000000000000000000) + (211297043 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13219 166) (d.f1 13219 166) d.f2 ≤
      ((1036506141 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1036506141 / 250000000000000000)) * ((1383183803 / 1000000000000000000)) * (126 / 100) +
      2 * (((1383183803 / 1000000000000000000)) ^ 2 + 2 * ((1036506141 / 250000000000000000)) * ((33244873 / 100000000000000000))) +
      6 * ((1383183803 / 1000000000000000000)) * ((33244873 / 100000000000000000)) * (126 / 100) + 8 * ((33244873 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13219 166) (d.f1 13219 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13219 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13219 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13219 166) (d.f1 13219 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13219 166) (d.w1 13219 166) (d.w2 13219 166)
  have hwexpr0 : 0 ≤ d.w0 13219 166 + d.w1 13219 166 * √(π / 2) +
      2 * d.w2 13219 166 + energyR16 13219 *
      radiusPolynomialRoot16 (d.w0 13219 166) (d.w1 13219 166) (d.w2 13219 166) := by
    positivity
  constructor
  · change (13219 : ℝ) ^ 8 * (mA 13219 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13219 166) (d.f1 13219 166) d.f2 + locationR16 13219 *
        radiusPolynomialRoot16 (d.f0 13219 166) (d.f1 13219 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13219 : ℝ) ^ 8 * (mA 13219 : ℝ) ^ 8 *
        ((((1036506141 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1036506141 / 250000000000000000)) * ((1383183803 / 1000000000000000000)) * (126 / 100) +
          2 * (((1383183803 / 1000000000000000000)) ^ 2 + 2 * ((1036506141 / 250000000000000000)) * ((33244873 / 100000000000000000))) +
          6 * ((1383183803 / 1000000000000000000)) * ((33244873 / 100000000000000000)) * (126 / 100) + 8 * ((33244873 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13219) *
          (32 * (((1036506141 / 250000000000000000) : ℝ) + (1383183803 / 1000000000000000000) + (33244873 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13219 : ℝ) ^ 16 *
      (d.w0 13219 166 + d.w1 13219 166 * √(π / 2) + 2 * d.w2 13219 166 +
        energyR16 13219 * radiusPolynomialRoot16 (d.w0 13219 166) (d.w1 13219 166)
          (d.w2 13219 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13219 : ℝ) ^ 16 *
        (((32512649 / 2000000000000000000) : ℝ) + ((1156606383 / 100000000000000000000)) * (126 / 100) + 2 * ((211297043 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13219) *
          (32 * (((32512649 / 2000000000000000000) : ℝ) + (1156606383 / 100000000000000000000) + (211297043 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13219

/-! A coarse bound on the actual paper statistics constant at dimension 13220. -/
namespace BstLean.Part266.Row13220
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13218 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13218 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13218 128 ≤ (13472 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13472 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13220) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13220 : ℕ))
    (by norm_num : (13220 : ℕ) ≤ 16384)
  have ht : paperTail256 13220 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13220 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13220 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13220 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13220 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13220 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13218 128 * √(2 / (13220 : ℝ)) *
      (√(13220 : ℝ) + paperT0 13220 + paperTail256 13220) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13220 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13220 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13220 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13218 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13218 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13220 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13220

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13220
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13220 (61 / 100) 166 (17 / (100 * 13220)) (26 / (10 * 13220)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13220 (61 / 100) 166 (17 / (100 * 13220)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (211247299 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (159793723 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3705893167 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13220 / 13220 * (61 / 100)) ^ 4 * inverseRadius8 (13220 - 1) /
            envelopeGap 13220 (61 / 100) 166 (17 / (100 * 13220)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13220

namespace BstLean.Part266.Row13220
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13220 166 ≤ (1295387 / 312500000000000)
  f1 : (tableEnvelope C).f1 13220 166 ≤ (1382921743 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (332385803 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13220 166 ≤ (1625263131 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13220 166 ≤ (578171859 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13220 166 ≤ (105624547 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (211247299 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (211247299 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (159793723 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3705893167 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3585987 / 1000000000) : ℝ) ≤ √(17 / (100 * 13220) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13220) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2055467339 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (35754017733 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13220) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13220) ≤ (26743827 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13220) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13220 * (166 : ℝ) ^ 2 + 26 / (10 * 13220) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13220) : ℝ)) (tA 13220 * 166 ^ 2 + 26 / (10 * 13220)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3585987 / 1000000000))) * ((211247299 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3585987 / 1000000000)) ^ 3) * ((159793723 / 125000000000000000000000))) + ((3705893167 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3585987 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13220) : ℝ)) d.D d.V d.P (√(tA 13220) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3585987 / 1000000000)) ^ 2 * (((2055467339 / 1000000000000000)) * ((35754017733 / 1000000000000000000)))) + ((3705893167 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13220) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3585987 / 1000000000)) * ((211247299 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13220) : ℝ)) (tA 13220 * 166 ^ 2 + 26 / (10 * 13220)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((211247299 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3585987 / 1000000000)) ^ 2) * ((159793723 / 125000000000000000000000)) + ((3705893167 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13220) : ℝ)) (√(26 / (10 * 13220) : ℝ)) d.D d.V d.P (√(tA 13220) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3585987 / 1000000000)) * (((2055467339 / 1000000000000000)) * ((35754017733 / 1000000000000000000))) + ((3705893167 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13220) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((211247299 / 50000000000000000000) : ℝ) + ((3705893167 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13220

namespace BstLean.Part266.Row13220
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13220 166 ∧
    0 ≤ (tableEnvelope C).f1 13220 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13220 166 ∧
    0 ≤ (tableEnvelope C).w1 13220 166 ∧ 0 ≤ (tableEnvelope C).w2 13220 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13220 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13220 166 ∧ 0 ≤ d.f1 13220 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13220 166 ∧ 0 ≤ d.w1 13220 166 ∧ 0 ≤ d.w2 13220 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13220 ≤ 2 * (228 / 100 : ℝ) / 13220 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13220 ≤ 2 * (370 / 100 : ℝ) / 13220 := by
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
    (completeRAData (tableEnvelope C) 13220 166).locationBound 13220 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13220 166).energyBound 13220 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13220 166) (d.f1 13220 166) d.f2 ≤
      32 * (((1295387 / 312500000000000) : ℝ) + (1382921743 / 1000000000000000000) + (332385803 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13220 166) (d.w1 13220 166)
      (d.w2 13220 166) ≤
      32 * (((1625263131 / 100000000000000000000) : ℝ) + (578171859 / 50000000000000000000) + (105624547 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13220 166) (d.f1 13220 166) d.f2 ≤
      ((1295387 / 312500000000000) : ℝ) ^ 2 + 2 * ((1295387 / 312500000000000)) * ((1382921743 / 1000000000000000000)) * (126 / 100) +
      2 * (((1382921743 / 1000000000000000000)) ^ 2 + 2 * ((1295387 / 312500000000000)) * ((332385803 / 1000000000000000000))) +
      6 * ((1382921743 / 1000000000000000000)) * ((332385803 / 1000000000000000000)) * (126 / 100) + 8 * ((332385803 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13220 166) (d.f1 13220 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13220 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13220 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13220 166) (d.f1 13220 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13220 166) (d.w1 13220 166) (d.w2 13220 166)
  have hwexpr0 : 0 ≤ d.w0 13220 166 + d.w1 13220 166 * √(π / 2) +
      2 * d.w2 13220 166 + energyR16 13220 *
      radiusPolynomialRoot16 (d.w0 13220 166) (d.w1 13220 166) (d.w2 13220 166) := by
    positivity
  constructor
  · change (13220 : ℝ) ^ 8 * (mA 13220 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13220 166) (d.f1 13220 166) d.f2 + locationR16 13220 *
        radiusPolynomialRoot16 (d.f0 13220 166) (d.f1 13220 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13220 : ℝ) ^ 8 * (mA 13220 : ℝ) ^ 8 *
        ((((1295387 / 312500000000000) : ℝ) ^ 2 + 2 * ((1295387 / 312500000000000)) * ((1382921743 / 1000000000000000000)) * (126 / 100) +
          2 * (((1382921743 / 1000000000000000000)) ^ 2 + 2 * ((1295387 / 312500000000000)) * ((332385803 / 1000000000000000000))) +
          6 * ((1382921743 / 1000000000000000000)) * ((332385803 / 1000000000000000000)) * (126 / 100) + 8 * ((332385803 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13220) *
          (32 * (((1295387 / 312500000000000) : ℝ) + (1382921743 / 1000000000000000000) + (332385803 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13220 : ℝ) ^ 16 *
      (d.w0 13220 166 + d.w1 13220 166 * √(π / 2) + 2 * d.w2 13220 166 +
        energyR16 13220 * radiusPolynomialRoot16 (d.w0 13220 166) (d.w1 13220 166)
          (d.w2 13220 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13220 : ℝ) ^ 16 *
        (((1625263131 / 100000000000000000000) : ℝ) + ((578171859 / 50000000000000000000)) * (126 / 100) + 2 * ((105624547 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13220) *
          (32 * (((1625263131 / 100000000000000000000) : ℝ) + (578171859 / 50000000000000000000) + (105624547 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13220

/-! A coarse bound on the actual paper statistics constant at dimension 13221. -/
namespace BstLean.Part266.Row13221
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13219 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13219 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13219 128 ≤ (13473 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13473 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13221) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13221 : ℕ))
    (by norm_num : (13221 : ℕ) ≤ 16384)
  have ht : paperTail256 13221 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13221 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13221 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13221 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13221 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13221 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13219 128 * √(2 / (13221 : ℝ)) *
      (√(13221 : ℝ) + paperT0 13221 + paperTail256 13221) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13221 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13221 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13221 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13219 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13219 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13221 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13221

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13221
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13221 (61 / 100) 166 (17 / (100 * 13221)) (26 / (10 * 13221)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13221 (61 / 100) 166 (17 / (100 * 13221)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (422398731 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1277963049 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (92590761 / 25000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13221 / 13221 * (61 / 100)) ^ 4 * inverseRadius8 (13221 - 1) /
            envelopeGap 13221 (61 / 100) 166 (17 / (100 * 13221)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13221

namespace BstLean.Part266.Row13221
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13221 166 ≤ (4144455827 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13221 166 ≤ (1382660533 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (166161493 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13221 166 ≤ (812447301 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13221 166 ≤ (1156081459 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13221 166 ≤ (422402319 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (422398731 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (422398731 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1277963049 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (92590761 / 25000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3585851 / 1000000000) : ℝ) ≤ √(17 / (100 * 13221) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13221) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1027617063 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (714972181 / 20000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13221) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13221) ≤ (6685451 / 62500000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13221) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13221 * (166 : ℝ) ^ 2 + 26 / (10 * 13221) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13221) : ℝ)) (tA 13221 * 166 ^ 2 + 26 / (10 * 13221)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3585851 / 1000000000))) * ((422398731 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3585851 / 1000000000)) ^ 3) * ((1277963049 / 1000000000000000000000000))) + ((92590761 / 25000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3585851 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13221) : ℝ)) d.D d.V d.P (√(tA 13221) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3585851 / 1000000000)) ^ 2 * (((1027617063 / 500000000000000)) * ((714972181 / 20000000000000000)))) + ((92590761 / 25000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13221) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3585851 / 1000000000)) * ((422398731 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13221) : ℝ)) (tA 13221 * 166 ^ 2 + 26 / (10 * 13221)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((422398731 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3585851 / 1000000000)) ^ 2) * ((1277963049 / 1000000000000000000000000)) + ((92590761 / 25000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13221) : ℝ)) (√(26 / (10 * 13221) : ℝ)) d.D d.V d.P (√(tA 13221) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3585851 / 1000000000)) * (((1027617063 / 500000000000000)) * ((714972181 / 20000000000000000))) + ((92590761 / 25000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13221) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((422398731 / 100000000000000000000) : ℝ) + ((92590761 / 25000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13221

namespace BstLean.Part266.Row13221
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13221 166 ∧
    0 ≤ (tableEnvelope C).f1 13221 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13221 166 ∧
    0 ≤ (tableEnvelope C).w1 13221 166 ∧ 0 ≤ (tableEnvelope C).w2 13221 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13221 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13221 166 ∧ 0 ≤ d.f1 13221 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13221 166 ∧ 0 ≤ d.w1 13221 166 ∧ 0 ≤ d.w2 13221 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13221 ≤ 2 * (228 / 100 : ℝ) / 13221 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13221 ≤ 2 * (370 / 100 : ℝ) / 13221 := by
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
    (completeRAData (tableEnvelope C) 13221 166).locationBound 13221 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13221 166).energyBound 13221 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13221 166) (d.f1 13221 166) d.f2 ≤
      32 * (((4144455827 / 1000000000000000000) : ℝ) + (1382660533 / 1000000000000000000) + (166161493 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13221 166) (d.w1 13221 166)
      (d.w2 13221 166) ≤
      32 * (((812447301 / 50000000000000000000) : ℝ) + (1156081459 / 100000000000000000000) + (422402319 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13221 166) (d.f1 13221 166) d.f2 ≤
      ((4144455827 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4144455827 / 1000000000000000000)) * ((1382660533 / 1000000000000000000)) * (126 / 100) +
      2 * (((1382660533 / 1000000000000000000)) ^ 2 + 2 * ((4144455827 / 1000000000000000000)) * ((166161493 / 500000000000000000))) +
      6 * ((1382660533 / 1000000000000000000)) * ((166161493 / 500000000000000000)) * (126 / 100) + 8 * ((166161493 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13221 166) (d.f1 13221 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13221 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13221 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13221 166) (d.f1 13221 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13221 166) (d.w1 13221 166) (d.w2 13221 166)
  have hwexpr0 : 0 ≤ d.w0 13221 166 + d.w1 13221 166 * √(π / 2) +
      2 * d.w2 13221 166 + energyR16 13221 *
      radiusPolynomialRoot16 (d.w0 13221 166) (d.w1 13221 166) (d.w2 13221 166) := by
    positivity
  constructor
  · change (13221 : ℝ) ^ 8 * (mA 13221 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13221 166) (d.f1 13221 166) d.f2 + locationR16 13221 *
        radiusPolynomialRoot16 (d.f0 13221 166) (d.f1 13221 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13221 : ℝ) ^ 8 * (mA 13221 : ℝ) ^ 8 *
        ((((4144455827 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4144455827 / 1000000000000000000)) * ((1382660533 / 1000000000000000000)) * (126 / 100) +
          2 * (((1382660533 / 1000000000000000000)) ^ 2 + 2 * ((4144455827 / 1000000000000000000)) * ((166161493 / 500000000000000000))) +
          6 * ((1382660533 / 1000000000000000000)) * ((166161493 / 500000000000000000)) * (126 / 100) + 8 * ((166161493 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13221) *
          (32 * (((4144455827 / 1000000000000000000) : ℝ) + (1382660533 / 1000000000000000000) + (166161493 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13221 : ℝ) ^ 16 *
      (d.w0 13221 166 + d.w1 13221 166 * √(π / 2) + 2 * d.w2 13221 166 +
        energyR16 13221 * radiusPolynomialRoot16 (d.w0 13221 166) (d.w1 13221 166)
          (d.w2 13221 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13221 : ℝ) ^ 16 *
        (((812447301 / 50000000000000000000) : ℝ) + ((1156081459 / 100000000000000000000)) * (126 / 100) + 2 * ((422402319 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13221) *
          (32 * (((812447301 / 50000000000000000000) : ℝ) + (1156081459 / 100000000000000000000) + (422402319 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13221

/-! A coarse bound on the actual paper statistics constant at dimension 13222. -/
namespace BstLean.Part266.Row13222
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13220 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13220 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13220 128 ≤ (13474 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13474 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13222) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13222 : ℕ))
    (by norm_num : (13222 : ℕ) ≤ 16384)
  have ht : paperTail256 13222 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13222 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13222 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13222 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13222 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13222 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13220 128 * √(2 / (13222 : ℝ)) *
      (√(13222 : ℝ) + paperT0 13222 + paperTail256 13222) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13222 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13222 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13222 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13220 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13220 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13222 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13222

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13222
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13222 (61 / 100) 166 (17 / (100 * 13222)) (26 / (10 * 13222)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13222 (61 / 100) 166 (17 / (100 * 13222)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (211151447 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1277576461 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (370136927 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13222 / 13222 * (61 / 100)) ^ 4 * inverseRadius8 (13222 - 1) /
            envelopeGap 13222 (61 / 100) 166 (17 / (100 * 13222)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13222

namespace BstLean.Part266.Row13222
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13222 166 ≤ (828734703 / 200000000000000000)
  f1 : (tableEnvelope C).f1 13222 166 ≤ (691199703 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (332260187 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13222 166 ≤ (1624526197 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13222 166 ≤ (231163857 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 13222 166 ≤ (5278831 / 1250000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (211151447 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (211151447 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1277576461 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (370136927 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((717143 / 200000000) : ℝ) ≤ √(17 / (100 * 13222) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13222) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2055000959 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (17871600803 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13222) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13222) ≤ (53479563 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13222) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13222 * (166 : ℝ) ^ 2 + 26 / (10 * 13222) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13222) : ℝ)) (tA 13222 * 166 ^ 2 + 26 / (10 * 13222)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((717143 / 200000000))) * ((211151447 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((717143 / 200000000)) ^ 3) * ((1277576461 / 1000000000000000000000000))) + ((370136927 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((717143 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13222) : ℝ)) d.D d.V d.P (√(tA 13222) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((717143 / 200000000)) ^ 2 * (((2055000959 / 1000000000000000)) * ((17871600803 / 500000000000000000)))) + ((370136927 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13222) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((717143 / 200000000)) * ((211151447 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13222) : ℝ)) (tA 13222 * 166 ^ 2 + 26 / (10 * 13222)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((211151447 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((717143 / 200000000)) ^ 2) * ((1277576461 / 1000000000000000000000000)) + ((370136927 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13222) : ℝ)) (√(26 / (10 * 13222) : ℝ)) d.D d.V d.P (√(tA 13222) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((717143 / 200000000)) * (((2055000959 / 1000000000000000)) * ((17871600803 / 500000000000000000))) + ((370136927 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13222) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((211151447 / 50000000000000000000) : ℝ) + ((370136927 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13222

namespace BstLean.Part266.Row13222
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13222 166 ∧
    0 ≤ (tableEnvelope C).f1 13222 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13222 166 ∧
    0 ≤ (tableEnvelope C).w1 13222 166 ∧ 0 ≤ (tableEnvelope C).w2 13222 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13222 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13222 166 ∧ 0 ≤ d.f1 13222 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13222 166 ∧ 0 ≤ d.w1 13222 166 ∧ 0 ≤ d.w2 13222 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13222 ≤ 2 * (228 / 100 : ℝ) / 13222 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13222 ≤ 2 * (370 / 100 : ℝ) / 13222 := by
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
    (completeRAData (tableEnvelope C) 13222 166).locationBound 13222 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13222 166).energyBound 13222 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13222 166) (d.f1 13222 166) d.f2 ≤
      32 * (((828734703 / 200000000000000000) : ℝ) + (691199703 / 500000000000000000) + (332260187 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13222 166) (d.w1 13222 166)
      (d.w2 13222 166) ≤
      32 * (((1624526197 / 100000000000000000000) : ℝ) + (231163857 / 20000000000000000000) + (5278831 / 1250000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13222 166) (d.f1 13222 166) d.f2 ≤
      ((828734703 / 200000000000000000) : ℝ) ^ 2 + 2 * ((828734703 / 200000000000000000)) * ((691199703 / 500000000000000000)) * (126 / 100) +
      2 * (((691199703 / 500000000000000000)) ^ 2 + 2 * ((828734703 / 200000000000000000)) * ((332260187 / 1000000000000000000))) +
      6 * ((691199703 / 500000000000000000)) * ((332260187 / 1000000000000000000)) * (126 / 100) + 8 * ((332260187 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13222 166) (d.f1 13222 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13222 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13222 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13222 166) (d.f1 13222 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13222 166) (d.w1 13222 166) (d.w2 13222 166)
  have hwexpr0 : 0 ≤ d.w0 13222 166 + d.w1 13222 166 * √(π / 2) +
      2 * d.w2 13222 166 + energyR16 13222 *
      radiusPolynomialRoot16 (d.w0 13222 166) (d.w1 13222 166) (d.w2 13222 166) := by
    positivity
  constructor
  · change (13222 : ℝ) ^ 8 * (mA 13222 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13222 166) (d.f1 13222 166) d.f2 + locationR16 13222 *
        radiusPolynomialRoot16 (d.f0 13222 166) (d.f1 13222 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13222 : ℝ) ^ 8 * (mA 13222 : ℝ) ^ 8 *
        ((((828734703 / 200000000000000000) : ℝ) ^ 2 + 2 * ((828734703 / 200000000000000000)) * ((691199703 / 500000000000000000)) * (126 / 100) +
          2 * (((691199703 / 500000000000000000)) ^ 2 + 2 * ((828734703 / 200000000000000000)) * ((332260187 / 1000000000000000000))) +
          6 * ((691199703 / 500000000000000000)) * ((332260187 / 1000000000000000000)) * (126 / 100) + 8 * ((332260187 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13222) *
          (32 * (((828734703 / 200000000000000000) : ℝ) + (691199703 / 500000000000000000) + (332260187 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13222 : ℝ) ^ 16 *
      (d.w0 13222 166 + d.w1 13222 166 * √(π / 2) + 2 * d.w2 13222 166 +
        energyR16 13222 * radiusPolynomialRoot16 (d.w0 13222 166) (d.w1 13222 166)
          (d.w2 13222 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13222 : ℝ) ^ 16 *
        (((1624526197 / 100000000000000000000) : ℝ) + ((231163857 / 20000000000000000000)) * (126 / 100) + 2 * ((5278831 / 1250000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13222) *
          (32 * (((1624526197 / 100000000000000000000) : ℝ) + (231163857 / 20000000000000000000) + (5278831 / 1250000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13222

/-! A coarse bound on the actual paper statistics constant at dimension 13223. -/
namespace BstLean.Part266.Row13223
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13221 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13221 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13221 128 ≤ (13475 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13475 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13223) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13223 : ℕ))
    (by norm_num : (13223 : ℕ) ≤ 16384)
  have ht : paperTail256 13223 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13223 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13223 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13223 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13223 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13223 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13221 128 * √(2 / (13223 : ℝ)) *
      (√(13223 : ℝ) + paperT0 13223 + paperTail256 13223) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13223 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13223 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13223 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13221 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13221 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13223 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13223

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13223
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13223 (61 / 100) 166 (17 / (100 * 13223)) (26 / (10 * 13223)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13223 (61 / 100) 166 (17 / (100 * 13223)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (84441417 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (63859501 / 50000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3699109653 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13223 / 13223 * (61 / 100)) ^ 4 * inverseRadius8 (13223 - 1) /
            envelopeGap 13223 (61 / 100) 166 (17 / (100 * 13223)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13223

namespace BstLean.Part266.Row13223
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13223 166 ≤ (4142888129 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13223 166 ≤ (345534397 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (332197313 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13223 166 ≤ (406039311 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 13223 166 ≤ (144444609 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 13223 166 ≤ (422210669 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (84441417 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (84441417 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (63859501 / 50000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3699109653 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((179279 / 50000000) : ℝ) ≤ √(17 / (100 * 13223) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13223) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1027383917 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (178688977 / 5000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13223) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13223) ≤ (53475519 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13223) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13223 * (166 : ℝ) ^ 2 + 26 / (10 * 13223) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13223) : ℝ)) (tA 13223 * 166 ^ 2 + 26 / (10 * 13223)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((179279 / 50000000))) * ((84441417 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((179279 / 50000000)) ^ 3) * ((63859501 / 50000000000000000000000))) + ((3699109653 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((179279 / 50000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13223) : ℝ)) d.D d.V d.P (√(tA 13223) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((179279 / 50000000)) ^ 2 * (((1027383917 / 500000000000000)) * ((178688977 / 5000000000000000)))) + ((3699109653 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13223) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((179279 / 50000000)) * ((84441417 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13223) : ℝ)) (tA 13223 * 166 ^ 2 + 26 / (10 * 13223)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((84441417 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((179279 / 50000000)) ^ 2) * ((63859501 / 50000000000000000000000)) + ((3699109653 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13223) : ℝ)) (√(26 / (10 * 13223) : ℝ)) d.D d.V d.P (√(tA 13223) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((179279 / 50000000)) * (((1027383917 / 500000000000000)) * ((178688977 / 5000000000000000))) + ((3699109653 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13223) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((84441417 / 20000000000000000000) : ℝ) + ((3699109653 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13223

namespace BstLean.Part266.Row13223
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13223 166 ∧
    0 ≤ (tableEnvelope C).f1 13223 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13223 166 ∧
    0 ≤ (tableEnvelope C).w1 13223 166 ∧ 0 ≤ (tableEnvelope C).w2 13223 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13223 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13223 166 ∧ 0 ≤ d.f1 13223 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13223 166 ∧ 0 ≤ d.w1 13223 166 ∧ 0 ≤ d.w2 13223 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13223 ≤ 2 * (228 / 100 : ℝ) / 13223 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13223 ≤ 2 * (370 / 100 : ℝ) / 13223 := by
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
    (completeRAData (tableEnvelope C) 13223 166).locationBound 13223 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13223 166).energyBound 13223 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13223 166) (d.f1 13223 166) d.f2 ≤
      32 * (((4142888129 / 1000000000000000000) : ℝ) + (345534397 / 250000000000000000) + (332197313 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13223 166) (d.w1 13223 166)
      (d.w2 13223 166) ≤
      32 * (((406039311 / 25000000000000000000) : ℝ) + (144444609 / 12500000000000000000) + (422210669 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13223 166) (d.f1 13223 166) d.f2 ≤
      ((4142888129 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4142888129 / 1000000000000000000)) * ((345534397 / 250000000000000000)) * (126 / 100) +
      2 * (((345534397 / 250000000000000000)) ^ 2 + 2 * ((4142888129 / 1000000000000000000)) * ((332197313 / 1000000000000000000))) +
      6 * ((345534397 / 250000000000000000)) * ((332197313 / 1000000000000000000)) * (126 / 100) + 8 * ((332197313 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13223 166) (d.f1 13223 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13223 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13223 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13223 166) (d.f1 13223 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13223 166) (d.w1 13223 166) (d.w2 13223 166)
  have hwexpr0 : 0 ≤ d.w0 13223 166 + d.w1 13223 166 * √(π / 2) +
      2 * d.w2 13223 166 + energyR16 13223 *
      radiusPolynomialRoot16 (d.w0 13223 166) (d.w1 13223 166) (d.w2 13223 166) := by
    positivity
  constructor
  · change (13223 : ℝ) ^ 8 * (mA 13223 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13223 166) (d.f1 13223 166) d.f2 + locationR16 13223 *
        radiusPolynomialRoot16 (d.f0 13223 166) (d.f1 13223 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13223 : ℝ) ^ 8 * (mA 13223 : ℝ) ^ 8 *
        ((((4142888129 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4142888129 / 1000000000000000000)) * ((345534397 / 250000000000000000)) * (126 / 100) +
          2 * (((345534397 / 250000000000000000)) ^ 2 + 2 * ((4142888129 / 1000000000000000000)) * ((332197313 / 1000000000000000000))) +
          6 * ((345534397 / 250000000000000000)) * ((332197313 / 1000000000000000000)) * (126 / 100) + 8 * ((332197313 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13223) *
          (32 * (((4142888129 / 1000000000000000000) : ℝ) + (345534397 / 250000000000000000) + (332197313 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13223 : ℝ) ^ 16 *
      (d.w0 13223 166 + d.w1 13223 166 * √(π / 2) + 2 * d.w2 13223 166 +
        energyR16 13223 * radiusPolynomialRoot16 (d.w0 13223 166) (d.w1 13223 166)
          (d.w2 13223 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13223 : ℝ) ^ 16 *
        (((406039311 / 25000000000000000000) : ℝ) + ((144444609 / 12500000000000000000)) * (126 / 100) + 2 * ((422210669 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13223) *
          (32 * (((406039311 / 25000000000000000000) : ℝ) + (144444609 / 12500000000000000000) + (422210669 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13223
