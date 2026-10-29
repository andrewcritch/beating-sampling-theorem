import BstLean.Part266Shard16Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12750. -/
namespace BstLean.Part266.Row12750
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12748 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12748 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12748 128 ≤ (13002 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13002 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12750) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12750 : ℕ))
    (by norm_num : (12750 : ℕ) ≤ 16384)
  have ht : paperTail256 12750 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12750 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12750 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12750 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12750 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12750 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12748 128 * √(2 / (12750 : ℝ)) *
      (√(12750 : ℝ) + paperT0 12750 + paperTail256 12750) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12750 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12750 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12750 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12748 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12748 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12750 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12750

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12750
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12750 (61 / 100) 163 (17 / (100 * 12750)) (26 / (10 * 12750)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12750 (61 / 100) 163 (17 / (100 * 12750)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (58870457 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (738766529 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2478792469 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12750 / 12750 * (61 / 100)) ^ 4 * inverseRadius8 (12750 - 1) /
            envelopeGap 12750 (61 / 100) 163 (17 / (100 * 12750)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12750

namespace BstLean.Part266.Row12750
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12750 163 ≤ (2268951979 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12750 163 ≤ (1513921499 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (90967893 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12750 163 ≤ (113232233 / 6250000000000000000)
  w1 : (tableEnvelope C).w1 12750 163 ≤ (1289001091 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12750 163 ≤ (470968459 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (58870457 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (58870457 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (738766529 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2478792469 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3651483 / 1000000000) : ℝ) ≤ √(17 / (100 * 12750) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12750) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (542542427 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (192193461 / 5000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12750) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12750) ≤ (110918711 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12750) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12750 * (163 : ℝ) ^ 2 + 26 / (10 * 12750) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12750) : ℝ)) (tA 12750 * 163 ^ 2 + 26 / (10 * 12750)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3651483 / 1000000000))) * ((58870457 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3651483 / 1000000000)) ^ 3) * ((738766529 / 500000000000000000000000))) + ((2478792469 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3651483 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12750) : ℝ)) d.D d.V d.P (√(tA 12750) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3651483 / 1000000000)) ^ 2 * (((542542427 / 250000000000000)) * ((192193461 / 5000000000000000)))) + ((2478792469 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12750) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3651483 / 1000000000)) * ((58870457 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12750) : ℝ)) (tA 12750 * 163 ^ 2 + 26 / (10 * 12750)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((58870457 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3651483 / 1000000000)) ^ 2) * ((738766529 / 500000000000000000000000)) + ((2478792469 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12750) : ℝ)) (√(26 / (10 * 12750) : ℝ)) d.D d.V d.P (√(tA 12750) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3651483 / 1000000000)) * (((542542427 / 250000000000000)) * ((192193461 / 5000000000000000))) + ((2478792469 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12750) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((58870457 / 12500000000000000000) : ℝ) + ((2478792469 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12750

namespace BstLean.Part266.Row12750
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12750 163 ∧
    0 ≤ (tableEnvelope C).f1 12750 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12750 163 ∧
    0 ≤ (tableEnvelope C).w1 12750 163 ∧ 0 ≤ (tableEnvelope C).w2 12750 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12750 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12750 163 ∧ 0 ≤ d.f1 12750 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12750 163 ∧ 0 ≤ d.w1 12750 163 ∧ 0 ≤ d.w2 12750 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12750 ≤ 2 * (228 / 100 : ℝ) / 12750 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12750 ≤ 2 * (370 / 100 : ℝ) / 12750 := by
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
    (completeRAData (tableEnvelope C) 12750 163).locationBound 12750 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12750 163).energyBound 12750 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12750 163) (d.f1 12750 163) d.f2 ≤
      32 * (((2268951979 / 500000000000000000) : ℝ) + (1513921499 / 1000000000000000000) + (90967893 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12750 163) (d.w1 12750 163)
      (d.w2 12750 163) ≤
      32 * (((113232233 / 6250000000000000000) : ℝ) + (1289001091 / 100000000000000000000) + (470968459 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12750 163) (d.f1 12750 163) d.f2 ≤
      ((2268951979 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2268951979 / 500000000000000000)) * ((1513921499 / 1000000000000000000)) * (126 / 100) +
      2 * (((1513921499 / 1000000000000000000)) ^ 2 + 2 * ((2268951979 / 500000000000000000)) * ((90967893 / 250000000000000000))) +
      6 * ((1513921499 / 1000000000000000000)) * ((90967893 / 250000000000000000)) * (126 / 100) + 8 * ((90967893 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12750 163) (d.f1 12750 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12750 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12750 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12750 163) (d.f1 12750 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12750 163) (d.w1 12750 163) (d.w2 12750 163)
  have hwexpr0 : 0 ≤ d.w0 12750 163 + d.w1 12750 163 * √(π / 2) +
      2 * d.w2 12750 163 + energyR16 12750 *
      radiusPolynomialRoot16 (d.w0 12750 163) (d.w1 12750 163) (d.w2 12750 163) := by
    positivity
  constructor
  · change (12750 : ℝ) ^ 8 * (mA 12750 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12750 163) (d.f1 12750 163) d.f2 + locationR16 12750 *
        radiusPolynomialRoot16 (d.f0 12750 163) (d.f1 12750 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12750 : ℝ) ^ 8 * (mA 12750 : ℝ) ^ 8 *
        ((((2268951979 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2268951979 / 500000000000000000)) * ((1513921499 / 1000000000000000000)) * (126 / 100) +
          2 * (((1513921499 / 1000000000000000000)) ^ 2 + 2 * ((2268951979 / 500000000000000000)) * ((90967893 / 250000000000000000))) +
          6 * ((1513921499 / 1000000000000000000)) * ((90967893 / 250000000000000000)) * (126 / 100) + 8 * ((90967893 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12750) *
          (32 * (((2268951979 / 500000000000000000) : ℝ) + (1513921499 / 1000000000000000000) + (90967893 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12750 : ℝ) ^ 16 *
      (d.w0 12750 163 + d.w1 12750 163 * √(π / 2) + 2 * d.w2 12750 163 +
        energyR16 12750 * radiusPolynomialRoot16 (d.w0 12750 163) (d.w1 12750 163)
          (d.w2 12750 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12750 : ℝ) ^ 16 *
        (((113232233 / 6250000000000000000) : ℝ) + ((1289001091 / 100000000000000000000)) * (126 / 100) + 2 * ((470968459 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12750) *
          (32 * (((113232233 / 6250000000000000000) : ℝ) + (1289001091 / 100000000000000000000) + (470968459 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12750

/-! A coarse bound on the actual paper statistics constant at dimension 12751. -/
namespace BstLean.Part266.Row12751
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12749 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12749 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12749 128 ≤ (13003 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13003 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12751) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12751 : ℕ))
    (by norm_num : (12751 : ℕ) ≤ 16384)
  have ht : paperTail256 12751 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12751 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12751 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12751 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12751 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12751 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12749 128 * √(2 / (12751 : ℝ)) *
      (√(12751 : ℝ) + paperT0 12751 + paperTail256 12751) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12751 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12751 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12751 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12749 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12749 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12751 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12751

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12751
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12751 (61 / 100) 163 (17 / (100 * 12751)) (26 / (10 * 12751)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12751 (61 / 100) 163 (17 / (100 * 12751)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (117713213 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1477069591 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (619305669 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12751 / 12751 * (61 / 100)) ^ 4 * inverseRadius8 (12751 - 1) /
            envelopeGap 12751 (61 / 100) 163 (17 / (100 * 12751)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12751

namespace BstLean.Part266.Row12751
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12751 163 ≤ (70890837 / 15625000000000000)
  f1 : (tableEnvelope C).f1 12751 163 ≤ (756812259 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (363800211 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12751 163 ≤ (1811289349 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12751 163 ≤ (1288697761 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12751 163 ≤ (117714413 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (117713213 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (117713213 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1477069591 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (619305669 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((182567 / 50000000) : ℝ) ≤ √(17 / (100 * 12751) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12751) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (542478601 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1537306523 / 40000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12751) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12751) ≤ (27727503 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12751) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12751 * (163 : ℝ) ^ 2 + 26 / (10 * 12751) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12751) : ℝ)) (tA 12751 * 163 ^ 2 + 26 / (10 * 12751)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((182567 / 50000000))) * ((117713213 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((182567 / 50000000)) ^ 3) * ((1477069591 / 1000000000000000000000000))) + ((619305669 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((182567 / 50000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12751) : ℝ)) d.D d.V d.P (√(tA 12751) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((182567 / 50000000)) ^ 2 * (((542478601 / 250000000000000)) * ((1537306523 / 40000000000000000)))) + ((619305669 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12751) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((182567 / 50000000)) * ((117713213 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12751) : ℝ)) (tA 12751 * 163 ^ 2 + 26 / (10 * 12751)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((117713213 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((182567 / 50000000)) ^ 2) * ((1477069591 / 1000000000000000000000000)) + ((619305669 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12751) : ℝ)) (√(26 / (10 * 12751) : ℝ)) d.D d.V d.P (√(tA 12751) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((182567 / 50000000)) * (((542478601 / 250000000000000)) * ((1537306523 / 40000000000000000))) + ((619305669 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12751) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((117713213 / 25000000000000000000) : ℝ) + ((619305669 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12751

namespace BstLean.Part266.Row12751
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12751 163 ∧
    0 ≤ (tableEnvelope C).f1 12751 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12751 163 ∧
    0 ≤ (tableEnvelope C).w1 12751 163 ∧ 0 ≤ (tableEnvelope C).w2 12751 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12751 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12751 163 ∧ 0 ≤ d.f1 12751 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12751 163 ∧ 0 ≤ d.w1 12751 163 ∧ 0 ≤ d.w2 12751 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12751 ≤ 2 * (228 / 100 : ℝ) / 12751 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12751 ≤ 2 * (370 / 100 : ℝ) / 12751 := by
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
    (completeRAData (tableEnvelope C) 12751 163).locationBound 12751 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12751 163).energyBound 12751 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12751 163) (d.f1 12751 163) d.f2 ≤
      32 * (((70890837 / 15625000000000000) : ℝ) + (756812259 / 500000000000000000) + (363800211 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12751 163) (d.w1 12751 163)
      (d.w2 12751 163) ≤
      32 * (((1811289349 / 100000000000000000000) : ℝ) + (1288697761 / 100000000000000000000) + (117714413 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12751 163) (d.f1 12751 163) d.f2 ≤
      ((70890837 / 15625000000000000) : ℝ) ^ 2 + 2 * ((70890837 / 15625000000000000)) * ((756812259 / 500000000000000000)) * (126 / 100) +
      2 * (((756812259 / 500000000000000000)) ^ 2 + 2 * ((70890837 / 15625000000000000)) * ((363800211 / 1000000000000000000))) +
      6 * ((756812259 / 500000000000000000)) * ((363800211 / 1000000000000000000)) * (126 / 100) + 8 * ((363800211 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12751 163) (d.f1 12751 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12751 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12751 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12751 163) (d.f1 12751 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12751 163) (d.w1 12751 163) (d.w2 12751 163)
  have hwexpr0 : 0 ≤ d.w0 12751 163 + d.w1 12751 163 * √(π / 2) +
      2 * d.w2 12751 163 + energyR16 12751 *
      radiusPolynomialRoot16 (d.w0 12751 163) (d.w1 12751 163) (d.w2 12751 163) := by
    positivity
  constructor
  · change (12751 : ℝ) ^ 8 * (mA 12751 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12751 163) (d.f1 12751 163) d.f2 + locationR16 12751 *
        radiusPolynomialRoot16 (d.f0 12751 163) (d.f1 12751 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12751 : ℝ) ^ 8 * (mA 12751 : ℝ) ^ 8 *
        ((((70890837 / 15625000000000000) : ℝ) ^ 2 + 2 * ((70890837 / 15625000000000000)) * ((756812259 / 500000000000000000)) * (126 / 100) +
          2 * (((756812259 / 500000000000000000)) ^ 2 + 2 * ((70890837 / 15625000000000000)) * ((363800211 / 1000000000000000000))) +
          6 * ((756812259 / 500000000000000000)) * ((363800211 / 1000000000000000000)) * (126 / 100) + 8 * ((363800211 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12751) *
          (32 * (((70890837 / 15625000000000000) : ℝ) + (756812259 / 500000000000000000) + (363800211 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12751 : ℝ) ^ 16 *
      (d.w0 12751 163 + d.w1 12751 163 * √(π / 2) + 2 * d.w2 12751 163 +
        energyR16 12751 * radiusPolynomialRoot16 (d.w0 12751 163) (d.w1 12751 163)
          (d.w2 12751 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12751 : ℝ) ^ 16 *
        (((1811289349 / 100000000000000000000) : ℝ) + ((1288697761 / 100000000000000000000)) * (126 / 100) + 2 * ((117714413 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12751) *
          (32 * (((1811289349 / 100000000000000000000) : ℝ) + (1288697761 / 100000000000000000000) + (117714413 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12751

/-! A coarse bound on the actual paper statistics constant at dimension 12752. -/
namespace BstLean.Part266.Row12752
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12750 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12750 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12750 128 ≤ (13004 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13004 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12752) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12752 : ℕ))
    (by norm_num : (12752 : ℕ) ≤ 16384)
  have ht : paperTail256 12752 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12752 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12752 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12752 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12752 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12752 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12750 128 * √(2 / (12752 : ℝ)) *
      (√(12752 : ℝ) + paperT0 12752 + paperTail256 12752) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12752 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12752 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12752 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12750 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12750 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12752 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12752

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12752
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12752 (61 / 100) 163 (17 / (100 * 12752)) (26 / (10 * 12752)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12752 (61 / 100) 163 (17 / (100 * 12752)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (117685521 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (738303153 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1237827001 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12752 / 12752 * (61 / 100)) ^ 4 * inverseRadius8 (12752 - 1) /
            envelopeGap 12752 (61 / 100) 163 (17 / (100 * 12752)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12752

namespace BstLean.Part266.Row12752
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12752 163 ≤ (907224697 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12752 163 ≤ (756663817 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (45466109 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12752 163 ≤ (1810863117 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12752 163 ≤ (644197267 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12752 163 ≤ (470746881 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (117685521 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (117685521 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (738303153 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1237827001 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3651197 / 1000000000) : ℝ) ≤ √(17 / (100 * 12752) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12752) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2169659153 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9606658843 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12752) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12752) ≤ (22180263 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12752) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12752 * (163 : ℝ) ^ 2 + 26 / (10 * 12752) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12752) : ℝ)) (tA 12752 * 163 ^ 2 + 26 / (10 * 12752)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3651197 / 1000000000))) * ((117685521 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3651197 / 1000000000)) ^ 3) * ((738303153 / 500000000000000000000000))) + ((1237827001 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3651197 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12752) : ℝ)) d.D d.V d.P (√(tA 12752) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3651197 / 1000000000)) ^ 2 * (((2169659153 / 1000000000000000)) * ((9606658843 / 250000000000000000)))) + ((1237827001 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12752) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3651197 / 1000000000)) * ((117685521 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12752) : ℝ)) (tA 12752 * 163 ^ 2 + 26 / (10 * 12752)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((117685521 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3651197 / 1000000000)) ^ 2) * ((738303153 / 500000000000000000000000)) + ((1237827001 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12752) : ℝ)) (√(26 / (10 * 12752) : ℝ)) d.D d.V d.P (√(tA 12752) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3651197 / 1000000000)) * (((2169659153 / 1000000000000000)) * ((9606658843 / 250000000000000000))) + ((1237827001 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12752) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((117685521 / 25000000000000000000) : ℝ) + ((1237827001 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12752

namespace BstLean.Part266.Row12752
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12752 163 ∧
    0 ≤ (tableEnvelope C).f1 12752 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12752 163 ∧
    0 ≤ (tableEnvelope C).w1 12752 163 ∧ 0 ≤ (tableEnvelope C).w2 12752 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12752 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12752 163 ∧ 0 ≤ d.f1 12752 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12752 163 ∧ 0 ≤ d.w1 12752 163 ∧ 0 ≤ d.w2 12752 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12752 ≤ 2 * (228 / 100 : ℝ) / 12752 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12752 ≤ 2 * (370 / 100 : ℝ) / 12752 := by
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
    (completeRAData (tableEnvelope C) 12752 163).locationBound 12752 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12752 163).energyBound 12752 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12752 163) (d.f1 12752 163) d.f2 ≤
      32 * (((907224697 / 200000000000000000) : ℝ) + (756663817 / 500000000000000000) + (45466109 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12752 163) (d.w1 12752 163)
      (d.w2 12752 163) ≤
      32 * (((1810863117 / 100000000000000000000) : ℝ) + (644197267 / 50000000000000000000) + (470746881 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12752 163) (d.f1 12752 163) d.f2 ≤
      ((907224697 / 200000000000000000) : ℝ) ^ 2 + 2 * ((907224697 / 200000000000000000)) * ((756663817 / 500000000000000000)) * (126 / 100) +
      2 * (((756663817 / 500000000000000000)) ^ 2 + 2 * ((907224697 / 200000000000000000)) * ((45466109 / 125000000000000000))) +
      6 * ((756663817 / 500000000000000000)) * ((45466109 / 125000000000000000)) * (126 / 100) + 8 * ((45466109 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12752 163) (d.f1 12752 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12752 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12752 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12752 163) (d.f1 12752 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12752 163) (d.w1 12752 163) (d.w2 12752 163)
  have hwexpr0 : 0 ≤ d.w0 12752 163 + d.w1 12752 163 * √(π / 2) +
      2 * d.w2 12752 163 + energyR16 12752 *
      radiusPolynomialRoot16 (d.w0 12752 163) (d.w1 12752 163) (d.w2 12752 163) := by
    positivity
  constructor
  · change (12752 : ℝ) ^ 8 * (mA 12752 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12752 163) (d.f1 12752 163) d.f2 + locationR16 12752 *
        radiusPolynomialRoot16 (d.f0 12752 163) (d.f1 12752 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12752 : ℝ) ^ 8 * (mA 12752 : ℝ) ^ 8 *
        ((((907224697 / 200000000000000000) : ℝ) ^ 2 + 2 * ((907224697 / 200000000000000000)) * ((756663817 / 500000000000000000)) * (126 / 100) +
          2 * (((756663817 / 500000000000000000)) ^ 2 + 2 * ((907224697 / 200000000000000000)) * ((45466109 / 125000000000000000))) +
          6 * ((756663817 / 500000000000000000)) * ((45466109 / 125000000000000000)) * (126 / 100) + 8 * ((45466109 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12752) *
          (32 * (((907224697 / 200000000000000000) : ℝ) + (756663817 / 500000000000000000) + (45466109 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12752 : ℝ) ^ 16 *
      (d.w0 12752 163 + d.w1 12752 163 * √(π / 2) + 2 * d.w2 12752 163 +
        energyR16 12752 * radiusPolynomialRoot16 (d.w0 12752 163) (d.w1 12752 163)
          (d.w2 12752 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12752 : ℝ) ^ 16 *
        (((1810863117 / 100000000000000000000) : ℝ) + ((644197267 / 50000000000000000000)) * (126 / 100) + 2 * ((470746881 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12752) *
          (32 * (((1810863117 / 100000000000000000000) : ℝ) + (644197267 / 50000000000000000000) + (470746881 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12752

/-! A coarse bound on the actual paper statistics constant at dimension 12753. -/
namespace BstLean.Part266.Row12753
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12751 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12751 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12751 128 ≤ (13005 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13005 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12753) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12753 : ℕ))
    (by norm_num : (12753 : ℕ) ≤ 16384)
  have ht : paperTail256 12753 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12753 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12753 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12753 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12753 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12753 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12751 128 * √(2 / (12753 : ℝ)) *
      (√(12753 : ℝ) + paperT0 12753 + paperTail256 12753) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12753 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12753 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12753 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12751 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12751 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12753 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12753

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12753
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12753 (61 / 100) 163 (17 / (100 * 12753)) (26 / (10 * 12753)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12753 (61 / 100) 163 (17 / (100 * 12753)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (9412627 / 2000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (738071601 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2474086447 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12753 / 12753 * (61 / 100)) ^ 4 * inverseRadius8 (12753 - 1) /
            envelopeGap 12753 (61 / 100) 163 (17 / (100 * 12753)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12753

namespace BstLean.Part266.Row12753
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12753 163 ≤ (566904213 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12753 163 ≤ (378257711 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (181828777 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12753 163 ≤ (1810437029 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12753 163 ≤ (1288091407 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12753 163 ≤ (29414759 / 6250000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (9412627 / 2000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (9412627 / 2000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (738071601 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2474086447 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1825527 / 500000000) : ℝ) ≤ √(17 / (100 * 12753) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12753) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2169403951 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38420609079 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12753) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12753) ≤ (110892619 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12753) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12753 * (163 : ℝ) ^ 2 + 26 / (10 * 12753) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12753) : ℝ)) (tA 12753 * 163 ^ 2 + 26 / (10 * 12753)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1825527 / 500000000))) * ((9412627 / 2000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1825527 / 500000000)) ^ 3) * ((738071601 / 500000000000000000000000))) + ((2474086447 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1825527 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12753) : ℝ)) d.D d.V d.P (√(tA 12753) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1825527 / 500000000)) ^ 2 * (((2169403951 / 1000000000000000)) * ((38420609079 / 1000000000000000000)))) + ((2474086447 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12753) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1825527 / 500000000)) * ((9412627 / 2000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12753) : ℝ)) (tA 12753 * 163 ^ 2 + 26 / (10 * 12753)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((9412627 / 2000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1825527 / 500000000)) ^ 2) * ((738071601 / 500000000000000000000000)) + ((2474086447 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12753) : ℝ)) (√(26 / (10 * 12753) : ℝ)) d.D d.V d.P (√(tA 12753) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1825527 / 500000000)) * (((2169403951 / 1000000000000000)) * ((38420609079 / 1000000000000000000))) + ((2474086447 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12753) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((9412627 / 2000000000000000000) : ℝ) + ((2474086447 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12753

namespace BstLean.Part266.Row12753
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12753 163 ∧
    0 ≤ (tableEnvelope C).f1 12753 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12753 163 ∧
    0 ≤ (tableEnvelope C).w1 12753 163 ∧ 0 ≤ (tableEnvelope C).w2 12753 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12753 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12753 163 ∧ 0 ≤ d.f1 12753 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12753 163 ∧ 0 ≤ d.w1 12753 163 ∧ 0 ≤ d.w2 12753 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12753 ≤ 2 * (228 / 100 : ℝ) / 12753 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12753 ≤ 2 * (370 / 100 : ℝ) / 12753 := by
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
    (completeRAData (tableEnvelope C) 12753 163).locationBound 12753 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12753 163).energyBound 12753 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12753 163) (d.f1 12753 163) d.f2 ≤
      32 * (((566904213 / 125000000000000000) : ℝ) + (378257711 / 250000000000000000) + (181828777 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12753 163) (d.w1 12753 163)
      (d.w2 12753 163) ≤
      32 * (((1810437029 / 100000000000000000000) : ℝ) + (1288091407 / 100000000000000000000) + (29414759 / 6250000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12753 163) (d.f1 12753 163) d.f2 ≤
      ((566904213 / 125000000000000000) : ℝ) ^ 2 + 2 * ((566904213 / 125000000000000000)) * ((378257711 / 250000000000000000)) * (126 / 100) +
      2 * (((378257711 / 250000000000000000)) ^ 2 + 2 * ((566904213 / 125000000000000000)) * ((181828777 / 500000000000000000))) +
      6 * ((378257711 / 250000000000000000)) * ((181828777 / 500000000000000000)) * (126 / 100) + 8 * ((181828777 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12753 163) (d.f1 12753 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12753 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12753 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12753 163) (d.f1 12753 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12753 163) (d.w1 12753 163) (d.w2 12753 163)
  have hwexpr0 : 0 ≤ d.w0 12753 163 + d.w1 12753 163 * √(π / 2) +
      2 * d.w2 12753 163 + energyR16 12753 *
      radiusPolynomialRoot16 (d.w0 12753 163) (d.w1 12753 163) (d.w2 12753 163) := by
    positivity
  constructor
  · change (12753 : ℝ) ^ 8 * (mA 12753 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12753 163) (d.f1 12753 163) d.f2 + locationR16 12753 *
        radiusPolynomialRoot16 (d.f0 12753 163) (d.f1 12753 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12753 : ℝ) ^ 8 * (mA 12753 : ℝ) ^ 8 *
        ((((566904213 / 125000000000000000) : ℝ) ^ 2 + 2 * ((566904213 / 125000000000000000)) * ((378257711 / 250000000000000000)) * (126 / 100) +
          2 * (((378257711 / 250000000000000000)) ^ 2 + 2 * ((566904213 / 125000000000000000)) * ((181828777 / 500000000000000000))) +
          6 * ((378257711 / 250000000000000000)) * ((181828777 / 500000000000000000)) * (126 / 100) + 8 * ((181828777 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12753) *
          (32 * (((566904213 / 125000000000000000) : ℝ) + (378257711 / 250000000000000000) + (181828777 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12753 : ℝ) ^ 16 *
      (d.w0 12753 163 + d.w1 12753 163 * √(π / 2) + 2 * d.w2 12753 163 +
        energyR16 12753 * radiusPolynomialRoot16 (d.w0 12753 163) (d.w1 12753 163)
          (d.w2 12753 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12753 : ℝ) ^ 16 *
        (((1810437029 / 100000000000000000000) : ℝ) + ((1288091407 / 100000000000000000000)) * (126 / 100) + 2 * ((29414759 / 6250000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12753) *
          (32 * (((1810437029 / 100000000000000000000) : ℝ) + (1288091407 / 100000000000000000000) + (29414759 / 6250000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12753

/-! A coarse bound on the actual paper statistics constant at dimension 12754. -/
namespace BstLean.Part266.Row12754
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12752 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12752 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12752 128 ≤ (13006 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13006 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12754) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12754 : ℕ))
    (by norm_num : (12754 : ℕ) ≤ 16384)
  have ht : paperTail256 12754 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12754 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12754 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12754 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12754 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12754 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12752 128 * √(2 / (12754 : ℝ)) *
      (√(12754 : ℝ) + paperT0 12754 + paperTail256 12754) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12754 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12754 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12754 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12752 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12752 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12754 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12754

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12754
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12754 (61 / 100) 163 (17 / (100 * 12754)) (26 / (10 * 12754)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12754 (61 / 100) 163 (17 / (100 * 12754)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (470520651 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (36892007 / 25000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4945040019 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12754 / 12754 * (61 / 100)) ^ 4 * inverseRadius8 (12754 - 1) /
            envelopeGap 12754 (61 / 100) 163 (17 / (100 * 12754)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12754

namespace BstLean.Part266.Row12754
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12754 163 ≤ (4534344229 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12754 163 ≤ (30254683 / 20000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (363586257 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12754 163 ≤ (1810011089 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12754 163 ≤ (643894191 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12754 163 ≤ (235262721 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (470520651 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (470520651 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (36892007 / 25000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4945040019 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3650911 / 1000000000) : ℝ) ≤ √(17 / (100 * 12754) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12754) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2169148799 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3841458421 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12754) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12754) ≤ (27720981 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12754) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12754 * (163 : ℝ) ^ 2 + 26 / (10 * 12754) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12754) : ℝ)) (tA 12754 * 163 ^ 2 + 26 / (10 * 12754)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3650911 / 1000000000))) * ((470520651 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3650911 / 1000000000)) ^ 3) * ((36892007 / 25000000000000000000000))) + ((4945040019 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3650911 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12754) : ℝ)) d.D d.V d.P (√(tA 12754) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3650911 / 1000000000)) ^ 2 * (((2169148799 / 1000000000000000)) * ((3841458421 / 100000000000000000)))) + ((4945040019 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12754) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3650911 / 1000000000)) * ((470520651 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12754) : ℝ)) (tA 12754 * 163 ^ 2 + 26 / (10 * 12754)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((470520651 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3650911 / 1000000000)) ^ 2) * ((36892007 / 25000000000000000000000)) + ((4945040019 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12754) : ℝ)) (√(26 / (10 * 12754) : ℝ)) d.D d.V d.P (√(tA 12754) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3650911 / 1000000000)) * (((2169148799 / 1000000000000000)) * ((3841458421 / 100000000000000000))) + ((4945040019 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12754) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((470520651 / 100000000000000000000) : ℝ) + ((4945040019 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12754

namespace BstLean.Part266.Row12754
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12754 163 ∧
    0 ≤ (tableEnvelope C).f1 12754 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12754 163 ∧
    0 ≤ (tableEnvelope C).w1 12754 163 ∧ 0 ≤ (tableEnvelope C).w2 12754 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12754 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12754 163 ∧ 0 ≤ d.f1 12754 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12754 163 ∧ 0 ≤ d.w1 12754 163 ∧ 0 ≤ d.w2 12754 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12754 ≤ 2 * (228 / 100 : ℝ) / 12754 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12754 ≤ 2 * (370 / 100 : ℝ) / 12754 := by
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
    (completeRAData (tableEnvelope C) 12754 163).locationBound 12754 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12754 163).energyBound 12754 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12754 163) (d.f1 12754 163) d.f2 ≤
      32 * (((4534344229 / 1000000000000000000) : ℝ) + (30254683 / 20000000000000000) + (363586257 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12754 163) (d.w1 12754 163)
      (d.w2 12754 163) ≤
      32 * (((1810011089 / 100000000000000000000) : ℝ) + (643894191 / 50000000000000000000) + (235262721 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12754 163) (d.f1 12754 163) d.f2 ≤
      ((4534344229 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4534344229 / 1000000000000000000)) * ((30254683 / 20000000000000000)) * (126 / 100) +
      2 * (((30254683 / 20000000000000000)) ^ 2 + 2 * ((4534344229 / 1000000000000000000)) * ((363586257 / 1000000000000000000))) +
      6 * ((30254683 / 20000000000000000)) * ((363586257 / 1000000000000000000)) * (126 / 100) + 8 * ((363586257 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12754 163) (d.f1 12754 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12754 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12754 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12754 163) (d.f1 12754 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12754 163) (d.w1 12754 163) (d.w2 12754 163)
  have hwexpr0 : 0 ≤ d.w0 12754 163 + d.w1 12754 163 * √(π / 2) +
      2 * d.w2 12754 163 + energyR16 12754 *
      radiusPolynomialRoot16 (d.w0 12754 163) (d.w1 12754 163) (d.w2 12754 163) := by
    positivity
  constructor
  · change (12754 : ℝ) ^ 8 * (mA 12754 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12754 163) (d.f1 12754 163) d.f2 + locationR16 12754 *
        radiusPolynomialRoot16 (d.f0 12754 163) (d.f1 12754 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12754 : ℝ) ^ 8 * (mA 12754 : ℝ) ^ 8 *
        ((((4534344229 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4534344229 / 1000000000000000000)) * ((30254683 / 20000000000000000)) * (126 / 100) +
          2 * (((30254683 / 20000000000000000)) ^ 2 + 2 * ((4534344229 / 1000000000000000000)) * ((363586257 / 1000000000000000000))) +
          6 * ((30254683 / 20000000000000000)) * ((363586257 / 1000000000000000000)) * (126 / 100) + 8 * ((363586257 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12754) *
          (32 * (((4534344229 / 1000000000000000000) : ℝ) + (30254683 / 20000000000000000) + (363586257 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12754 : ℝ) ^ 16 *
      (d.w0 12754 163 + d.w1 12754 163 * √(π / 2) + 2 * d.w2 12754 163 +
        energyR16 12754 * radiusPolynomialRoot16 (d.w0 12754 163) (d.w1 12754 163)
          (d.w2 12754 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12754 : ℝ) ^ 16 *
        (((1810011089 / 100000000000000000000) : ℝ) + ((643894191 / 50000000000000000000)) * (126 / 100) + 2 * ((235262721 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12754) *
          (32 * (((1810011089 / 100000000000000000000) : ℝ) + (643894191 / 50000000000000000000) + (235262721 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12754

/-! A coarse bound on the actual paper statistics constant at dimension 12755. -/
namespace BstLean.Part266.Row12755
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12753 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12753 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12753 128 ≤ (13007 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13007 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12755) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12755 : ℕ))
    (by norm_num : (12755 : ℕ) ≤ 16384)
  have ht : paperTail256 12755 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12755 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12755 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12755 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12755 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12755 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12753 128 * √(2 / (12755 : ℝ)) *
      (√(12755 : ℝ) + paperT0 12755 + paperTail256 12755) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12755 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12755 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12755 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12753 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12753 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12755 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12755

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12755
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12755 (61 / 100) 163 (17 / (100 * 12755)) (26 / (10 * 12755)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12755 (61 / 100) 163 (17 / (100 * 12755)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (235204993 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1475217539 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2470954689 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12755 / 12755 * (61 / 100)) ^ 4 * inverseRadius8 (12755 - 1) /
            envelopeGap 12755 (61 / 100) 163 (17 / (100 * 12755)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12755

namespace BstLean.Part266.Row12755
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12755 163 ≤ (4533458641 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12755 163 ≤ (1512438379 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (9087877 / 25000000000000000)
  w0 : (tableEnvelope C).w0 12755 163 ≤ (904793013 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12755 163 ≤ (80467863 / 6250000000000000000)
  w2 : (tableEnvelope C).w2 12755 163 ≤ (235207387 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (235204993 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (235204993 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1475217539 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2470954689 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3650767 / 1000000000) : ℝ) ≤ √(17 / (100 * 12755) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12755) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (433778739 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (2400535047 / 62500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12755) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12755) ≤ (110875231 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12755) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12755 * (163 : ℝ) ^ 2 + 26 / (10 * 12755) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12755) : ℝ)) (tA 12755 * 163 ^ 2 + 26 / (10 * 12755)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3650767 / 1000000000))) * ((235204993 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3650767 / 1000000000)) ^ 3) * ((1475217539 / 1000000000000000000000000))) + ((2470954689 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3650767 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12755) : ℝ)) d.D d.V d.P (√(tA 12755) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3650767 / 1000000000)) ^ 2 * (((433778739 / 200000000000000)) * ((2400535047 / 62500000000000000)))) + ((2470954689 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12755) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3650767 / 1000000000)) * ((235204993 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12755) : ℝ)) (tA 12755 * 163 ^ 2 + 26 / (10 * 12755)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((235204993 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3650767 / 1000000000)) ^ 2) * ((1475217539 / 1000000000000000000000000)) + ((2470954689 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12755) : ℝ)) (√(26 / (10 * 12755) : ℝ)) d.D d.V d.P (√(tA 12755) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3650767 / 1000000000)) * (((433778739 / 200000000000000)) * ((2400535047 / 62500000000000000))) + ((2470954689 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12755) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((235204993 / 50000000000000000000) : ℝ) + ((2470954689 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12755

namespace BstLean.Part266.Row12755
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12755 163 ∧
    0 ≤ (tableEnvelope C).f1 12755 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12755 163 ∧
    0 ≤ (tableEnvelope C).w1 12755 163 ∧ 0 ≤ (tableEnvelope C).w2 12755 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12755 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12755 163 ∧ 0 ≤ d.f1 12755 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12755 163 ∧ 0 ≤ d.w1 12755 163 ∧ 0 ≤ d.w2 12755 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12755 ≤ 2 * (228 / 100 : ℝ) / 12755 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12755 ≤ 2 * (370 / 100 : ℝ) / 12755 := by
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
    (completeRAData (tableEnvelope C) 12755 163).locationBound 12755 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12755 163).energyBound 12755 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12755 163) (d.f1 12755 163) d.f2 ≤
      32 * (((4533458641 / 1000000000000000000) : ℝ) + (1512438379 / 1000000000000000000) + (9087877 / 25000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12755 163) (d.w1 12755 163)
      (d.w2 12755 163) ≤
      32 * (((904793013 / 50000000000000000000) : ℝ) + (80467863 / 6250000000000000000) + (235207387 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12755 163) (d.f1 12755 163) d.f2 ≤
      ((4533458641 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4533458641 / 1000000000000000000)) * ((1512438379 / 1000000000000000000)) * (126 / 100) +
      2 * (((1512438379 / 1000000000000000000)) ^ 2 + 2 * ((4533458641 / 1000000000000000000)) * ((9087877 / 25000000000000000))) +
      6 * ((1512438379 / 1000000000000000000)) * ((9087877 / 25000000000000000)) * (126 / 100) + 8 * ((9087877 / 25000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12755 163) (d.f1 12755 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12755 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12755 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12755 163) (d.f1 12755 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12755 163) (d.w1 12755 163) (d.w2 12755 163)
  have hwexpr0 : 0 ≤ d.w0 12755 163 + d.w1 12755 163 * √(π / 2) +
      2 * d.w2 12755 163 + energyR16 12755 *
      radiusPolynomialRoot16 (d.w0 12755 163) (d.w1 12755 163) (d.w2 12755 163) := by
    positivity
  constructor
  · change (12755 : ℝ) ^ 8 * (mA 12755 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12755 163) (d.f1 12755 163) d.f2 + locationR16 12755 *
        radiusPolynomialRoot16 (d.f0 12755 163) (d.f1 12755 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12755 : ℝ) ^ 8 * (mA 12755 : ℝ) ^ 8 *
        ((((4533458641 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4533458641 / 1000000000000000000)) * ((1512438379 / 1000000000000000000)) * (126 / 100) +
          2 * (((1512438379 / 1000000000000000000)) ^ 2 + 2 * ((4533458641 / 1000000000000000000)) * ((9087877 / 25000000000000000))) +
          6 * ((1512438379 / 1000000000000000000)) * ((9087877 / 25000000000000000)) * (126 / 100) + 8 * ((9087877 / 25000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12755) *
          (32 * (((4533458641 / 1000000000000000000) : ℝ) + (1512438379 / 1000000000000000000) + (9087877 / 25000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12755 : ℝ) ^ 16 *
      (d.w0 12755 163 + d.w1 12755 163 * √(π / 2) + 2 * d.w2 12755 163 +
        energyR16 12755 * radiusPolynomialRoot16 (d.w0 12755 163) (d.w1 12755 163)
          (d.w2 12755 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12755 : ℝ) ^ 16 *
        (((904793013 / 50000000000000000000) : ℝ) + ((80467863 / 6250000000000000000)) * (126 / 100) + 2 * ((235207387 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12755) *
          (32 * (((904793013 / 50000000000000000000) : ℝ) + (80467863 / 6250000000000000000) + (235207387 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12755

/-! A coarse bound on the actual paper statistics constant at dimension 12756. -/
namespace BstLean.Part266.Row12756
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12754 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12754 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12754 128 ≤ (13008 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13008 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12756) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12756 : ℕ))
    (by norm_num : (12756 : ℕ) ≤ 16384)
  have ht : paperTail256 12756 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12756 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12756 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12756 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12756 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12756 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12754 128 * √(2 / (12756 : ℝ)) *
      (√(12756 : ℝ) + paperT0 12756 + paperTail256 12756) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12756 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12756 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12756 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12754 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12754 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12756 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12756

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12756
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12756 (61 / 100) 163 (17 / (100 * 12756)) (26 / (10 * 12756)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12756 (61 / 100) 163 (17 / (100 * 12756)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (117574839 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (73737749 / 50000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (617347621 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12756 / 12756 * (61 / 100)) ^ 4 * inverseRadius8 (12756 - 1) /
            envelopeGap 12756 (61 / 100) 163 (17 / (100 * 12756)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12756

namespace BstLean.Part266.Row12756
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12756 163 ≤ (181302791 / 40000000000000000)
  f1 : (tableEnvelope C).f1 12756 163 ≤ (378035469 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (181721913 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12756 163 ≤ (1809160377 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12756 163 ≤ (257436597 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12756 163 ≤ (470304141 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (117574839 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (117574839 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (73737749 / 50000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (617347621 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((57041 / 15625000) : ℝ) ≤ √(17 / (100 * 12756) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12756) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2168638643 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38402538719 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12756) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12756) ≤ (110866539 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12756) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12756 * (163 : ℝ) ^ 2 + 26 / (10 * 12756) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12756) : ℝ)) (tA 12756 * 163 ^ 2 + 26 / (10 * 12756)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((57041 / 15625000))) * ((117574839 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((57041 / 15625000)) ^ 3) * ((73737749 / 50000000000000000000000))) + ((617347621 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((57041 / 15625000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12756) : ℝ)) d.D d.V d.P (√(tA 12756) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((57041 / 15625000)) ^ 2 * (((2168638643 / 1000000000000000)) * ((38402538719 / 1000000000000000000)))) + ((617347621 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12756) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((57041 / 15625000)) * ((117574839 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12756) : ℝ)) (tA 12756 * 163 ^ 2 + 26 / (10 * 12756)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((117574839 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((57041 / 15625000)) ^ 2) * ((73737749 / 50000000000000000000000)) + ((617347621 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12756) : ℝ)) (√(26 / (10 * 12756) : ℝ)) d.D d.V d.P (√(tA 12756) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((57041 / 15625000)) * (((2168638643 / 1000000000000000)) * ((38402538719 / 1000000000000000000))) + ((617347621 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12756) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((117574839 / 25000000000000000000) : ℝ) + ((617347621 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12756

namespace BstLean.Part266.Row12756
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12756 163 ∧
    0 ≤ (tableEnvelope C).f1 12756 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12756 163 ∧
    0 ≤ (tableEnvelope C).w1 12756 163 ∧ 0 ≤ (tableEnvelope C).w2 12756 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12756 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12756 163 ∧ 0 ≤ d.f1 12756 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12756 163 ∧ 0 ≤ d.w1 12756 163 ∧ 0 ≤ d.w2 12756 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12756 ≤ 2 * (228 / 100 : ℝ) / 12756 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12756 ≤ 2 * (370 / 100 : ℝ) / 12756 := by
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
    (completeRAData (tableEnvelope C) 12756 163).locationBound 12756 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12756 163).energyBound 12756 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12756 163) (d.f1 12756 163) d.f2 ≤
      32 * (((181302791 / 40000000000000000) : ℝ) + (378035469 / 250000000000000000) + (181721913 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12756 163) (d.w1 12756 163)
      (d.w2 12756 163) ≤
      32 * (((1809160377 / 100000000000000000000) : ℝ) + (257436597 / 20000000000000000000) + (470304141 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12756 163) (d.f1 12756 163) d.f2 ≤
      ((181302791 / 40000000000000000) : ℝ) ^ 2 + 2 * ((181302791 / 40000000000000000)) * ((378035469 / 250000000000000000)) * (126 / 100) +
      2 * (((378035469 / 250000000000000000)) ^ 2 + 2 * ((181302791 / 40000000000000000)) * ((181721913 / 500000000000000000))) +
      6 * ((378035469 / 250000000000000000)) * ((181721913 / 500000000000000000)) * (126 / 100) + 8 * ((181721913 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12756 163) (d.f1 12756 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12756 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12756 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12756 163) (d.f1 12756 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12756 163) (d.w1 12756 163) (d.w2 12756 163)
  have hwexpr0 : 0 ≤ d.w0 12756 163 + d.w1 12756 163 * √(π / 2) +
      2 * d.w2 12756 163 + energyR16 12756 *
      radiusPolynomialRoot16 (d.w0 12756 163) (d.w1 12756 163) (d.w2 12756 163) := by
    positivity
  constructor
  · change (12756 : ℝ) ^ 8 * (mA 12756 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12756 163) (d.f1 12756 163) d.f2 + locationR16 12756 *
        radiusPolynomialRoot16 (d.f0 12756 163) (d.f1 12756 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12756 : ℝ) ^ 8 * (mA 12756 : ℝ) ^ 8 *
        ((((181302791 / 40000000000000000) : ℝ) ^ 2 + 2 * ((181302791 / 40000000000000000)) * ((378035469 / 250000000000000000)) * (126 / 100) +
          2 * (((378035469 / 250000000000000000)) ^ 2 + 2 * ((181302791 / 40000000000000000)) * ((181721913 / 500000000000000000))) +
          6 * ((378035469 / 250000000000000000)) * ((181721913 / 500000000000000000)) * (126 / 100) + 8 * ((181721913 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12756) *
          (32 * (((181302791 / 40000000000000000) : ℝ) + (378035469 / 250000000000000000) + (181721913 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12756 : ℝ) ^ 16 *
      (d.w0 12756 163 + d.w1 12756 163 * √(π / 2) + 2 * d.w2 12756 163 +
        energyR16 12756 * radiusPolynomialRoot16 (d.w0 12756 163) (d.w1 12756 163)
          (d.w2 12756 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12756 : ℝ) ^ 16 *
        (((1809160377 / 100000000000000000000) : ℝ) + ((257436597 / 20000000000000000000)) * (126 / 100) + 2 * ((470304141 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12756) *
          (32 * (((1809160377 / 100000000000000000000) : ℝ) + (257436597 / 20000000000000000000) + (470304141 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12756

/-! A coarse bound on the actual paper statistics constant at dimension 12757. -/
namespace BstLean.Part266.Row12757
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12755 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12755 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12755 128 ≤ (13009 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13009 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12757) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12757 : ℕ))
    (by norm_num : (12757 : ℕ) ≤ 16384)
  have ht : paperTail256 12757 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12757 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12757 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12757 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12757 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12757 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12755 128 * √(2 / (12757 : ℝ)) *
      (√(12757 : ℝ) + paperT0 12757 + paperTail256 12757) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12757 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12757 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12757 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12755 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12755 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12757 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12757

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12757
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12757 (61 / 100) 163 (17 / (100 * 12757)) (26 / (10 * 12757)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12757 (61 / 100) 163 (17 / (100 * 12757)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (470188761 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (737146301 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4935654789 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12757 / 12757 * (61 / 100)) ^ 4 * inverseRadius8 (12757 - 1) /
            envelopeGap 12757 (61 / 100) 163 (17 / (100 * 12757)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12757

namespace BstLean.Part266.Row12757
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12757 163 ≤ (1132920303 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12757 163 ≤ (1511845467 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (22710787 / 62500000000000000)
  w0 : (tableEnvelope C).w0 12757 163 ≤ (904367437 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12757 163 ≤ (1286880261 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12757 163 ≤ (470193543 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (470188761 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (470188761 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (737146301 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4935654789 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3650481 / 1000000000) : ℝ) ≤ √(17 / (100 * 12757) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12757) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (54209591 / 25000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19198259049 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12757) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12757) ≤ (13857231 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12757) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12757 * (163 : ℝ) ^ 2 + 26 / (10 * 12757) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12757) : ℝ)) (tA 12757 * 163 ^ 2 + 26 / (10 * 12757)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3650481 / 1000000000))) * ((470188761 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3650481 / 1000000000)) ^ 3) * ((737146301 / 500000000000000000000000))) + ((4935654789 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3650481 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12757) : ℝ)) d.D d.V d.P (√(tA 12757) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3650481 / 1000000000)) ^ 2 * (((54209591 / 25000000000000)) * ((19198259049 / 500000000000000000)))) + ((4935654789 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12757) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3650481 / 1000000000)) * ((470188761 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12757) : ℝ)) (tA 12757 * 163 ^ 2 + 26 / (10 * 12757)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((470188761 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3650481 / 1000000000)) ^ 2) * ((737146301 / 500000000000000000000000)) + ((4935654789 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12757) : ℝ)) (√(26 / (10 * 12757) : ℝ)) d.D d.V d.P (√(tA 12757) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3650481 / 1000000000)) * (((54209591 / 25000000000000)) * ((19198259049 / 500000000000000000))) + ((4935654789 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12757) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((470188761 / 100000000000000000000) : ℝ) + ((4935654789 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12757

namespace BstLean.Part266.Row12757
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12757 163 ∧
    0 ≤ (tableEnvelope C).f1 12757 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12757 163 ∧
    0 ≤ (tableEnvelope C).w1 12757 163 ∧ 0 ≤ (tableEnvelope C).w2 12757 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12757 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12757 163 ∧ 0 ≤ d.f1 12757 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12757 163 ∧ 0 ≤ d.w1 12757 163 ∧ 0 ≤ d.w2 12757 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12757 ≤ 2 * (228 / 100 : ℝ) / 12757 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12757 ≤ 2 * (370 / 100 : ℝ) / 12757 := by
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
    (completeRAData (tableEnvelope C) 12757 163).locationBound 12757 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12757 163).energyBound 12757 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12757 163) (d.f1 12757 163) d.f2 ≤
      32 * (((1132920303 / 250000000000000000) : ℝ) + (1511845467 / 1000000000000000000) + (22710787 / 62500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12757 163) (d.w1 12757 163)
      (d.w2 12757 163) ≤
      32 * (((904367437 / 50000000000000000000) : ℝ) + (1286880261 / 100000000000000000000) + (470193543 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12757 163) (d.f1 12757 163) d.f2 ≤
      ((1132920303 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1132920303 / 250000000000000000)) * ((1511845467 / 1000000000000000000)) * (126 / 100) +
      2 * (((1511845467 / 1000000000000000000)) ^ 2 + 2 * ((1132920303 / 250000000000000000)) * ((22710787 / 62500000000000000))) +
      6 * ((1511845467 / 1000000000000000000)) * ((22710787 / 62500000000000000)) * (126 / 100) + 8 * ((22710787 / 62500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12757 163) (d.f1 12757 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12757 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12757 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12757 163) (d.f1 12757 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12757 163) (d.w1 12757 163) (d.w2 12757 163)
  have hwexpr0 : 0 ≤ d.w0 12757 163 + d.w1 12757 163 * √(π / 2) +
      2 * d.w2 12757 163 + energyR16 12757 *
      radiusPolynomialRoot16 (d.w0 12757 163) (d.w1 12757 163) (d.w2 12757 163) := by
    positivity
  constructor
  · change (12757 : ℝ) ^ 8 * (mA 12757 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12757 163) (d.f1 12757 163) d.f2 + locationR16 12757 *
        radiusPolynomialRoot16 (d.f0 12757 163) (d.f1 12757 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12757 : ℝ) ^ 8 * (mA 12757 : ℝ) ^ 8 *
        ((((1132920303 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1132920303 / 250000000000000000)) * ((1511845467 / 1000000000000000000)) * (126 / 100) +
          2 * (((1511845467 / 1000000000000000000)) ^ 2 + 2 * ((1132920303 / 250000000000000000)) * ((22710787 / 62500000000000000))) +
          6 * ((1511845467 / 1000000000000000000)) * ((22710787 / 62500000000000000)) * (126 / 100) + 8 * ((22710787 / 62500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12757) *
          (32 * (((1132920303 / 250000000000000000) : ℝ) + (1511845467 / 1000000000000000000) + (22710787 / 62500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12757 : ℝ) ^ 16 *
      (d.w0 12757 163 + d.w1 12757 163 * √(π / 2) + 2 * d.w2 12757 163 +
        energyR16 12757 * radiusPolynomialRoot16 (d.w0 12757 163) (d.w1 12757 163)
          (d.w2 12757 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12757 : ℝ) ^ 16 *
        (((904367437 / 50000000000000000000) : ℝ) + ((1286880261 / 100000000000000000000)) * (126 / 100) + 2 * ((470193543 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12757) *
          (32 * (((904367437 / 50000000000000000000) : ℝ) + (1286880261 / 100000000000000000000) + (470193543 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12757

/-! A coarse bound on the actual paper statistics constant at dimension 12758. -/
namespace BstLean.Part266.Row12758
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12756 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12756 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12756 128 ≤ (13010 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13010 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12758) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12758 : ℕ))
    (by norm_num : (12758 : ℕ) ≤ 16384)
  have ht : paperTail256 12758 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12758 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12758 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12758 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12758 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12758 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12756 128 * √(2 / (12758 : ℝ)) *
      (√(12758 : ℝ) + paperT0 12758 + paperTail256 12758) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12758 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12758 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12758 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12756 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12756 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12758 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12758

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12758
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12758 (61 / 100) 163 (17 / (100 * 12758)) (26 / (10 * 12758)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12758 (61 / 100) 163 (17 / (100 * 12758)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (470078201 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (294766081 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2466265419 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12758 / 12758 * (61 / 100)) ^ 4 * inverseRadius8 (12758 - 1) /
            envelopeGap 12758 (61 / 100) 163 (17 / (100 * 12758)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12758

namespace BstLean.Part266.Row12758
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12758 163 ≤ (4530792953 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12758 163 ≤ (302309831 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (363301381 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12758 163 ≤ (452077379 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12758 163 ≤ (32164441 / 2500000000000000000)
  w2 : (tableEnvelope C).w2 12758 163 ≤ (23504149 / 5000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (470078201 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (470078201 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (294766081 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2466265419 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1825169 / 500000000) : ℝ) ≤ √(17 / (100 * 12758) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12758) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2168128689 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3839049889 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12758) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12758) ≤ (110849159 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12758) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12758 * (163 : ℝ) ^ 2 + 26 / (10 * 12758) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12758) : ℝ)) (tA 12758 * 163 ^ 2 + 26 / (10 * 12758)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1825169 / 500000000))) * ((470078201 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1825169 / 500000000)) ^ 3) * ((294766081 / 200000000000000000000000))) + ((2466265419 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1825169 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12758) : ℝ)) d.D d.V d.P (√(tA 12758) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1825169 / 500000000)) ^ 2 * (((2168128689 / 1000000000000000)) * ((3839049889 / 100000000000000000)))) + ((2466265419 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12758) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1825169 / 500000000)) * ((470078201 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12758) : ℝ)) (tA 12758 * 163 ^ 2 + 26 / (10 * 12758)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((470078201 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1825169 / 500000000)) ^ 2) * ((294766081 / 200000000000000000000000)) + ((2466265419 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12758) : ℝ)) (√(26 / (10 * 12758) : ℝ)) d.D d.V d.P (√(tA 12758) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1825169 / 500000000)) * (((2168128689 / 1000000000000000)) * ((3839049889 / 100000000000000000))) + ((2466265419 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12758) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((470078201 / 100000000000000000000) : ℝ) + ((2466265419 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12758

namespace BstLean.Part266.Row12758
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12758 163 ∧
    0 ≤ (tableEnvelope C).f1 12758 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12758 163 ∧
    0 ≤ (tableEnvelope C).w1 12758 163 ∧ 0 ≤ (tableEnvelope C).w2 12758 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12758 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12758 163 ∧ 0 ≤ d.f1 12758 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12758 163 ∧ 0 ≤ d.w1 12758 163 ∧ 0 ≤ d.w2 12758 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12758 ≤ 2 * (228 / 100 : ℝ) / 12758 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12758 ≤ 2 * (370 / 100 : ℝ) / 12758 := by
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
    (completeRAData (tableEnvelope C) 12758 163).locationBound 12758 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12758 163).energyBound 12758 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12758 163) (d.f1 12758 163) d.f2 ≤
      32 * (((4530792953 / 1000000000000000000) : ℝ) + (302309831 / 200000000000000000) + (363301381 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12758 163) (d.w1 12758 163)
      (d.w2 12758 163) ≤
      32 * (((452077379 / 25000000000000000000) : ℝ) + (32164441 / 2500000000000000000) + (23504149 / 5000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12758 163) (d.f1 12758 163) d.f2 ≤
      ((4530792953 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4530792953 / 1000000000000000000)) * ((302309831 / 200000000000000000)) * (126 / 100) +
      2 * (((302309831 / 200000000000000000)) ^ 2 + 2 * ((4530792953 / 1000000000000000000)) * ((363301381 / 1000000000000000000))) +
      6 * ((302309831 / 200000000000000000)) * ((363301381 / 1000000000000000000)) * (126 / 100) + 8 * ((363301381 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12758 163) (d.f1 12758 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12758 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12758 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12758 163) (d.f1 12758 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12758 163) (d.w1 12758 163) (d.w2 12758 163)
  have hwexpr0 : 0 ≤ d.w0 12758 163 + d.w1 12758 163 * √(π / 2) +
      2 * d.w2 12758 163 + energyR16 12758 *
      radiusPolynomialRoot16 (d.w0 12758 163) (d.w1 12758 163) (d.w2 12758 163) := by
    positivity
  constructor
  · change (12758 : ℝ) ^ 8 * (mA 12758 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12758 163) (d.f1 12758 163) d.f2 + locationR16 12758 *
        radiusPolynomialRoot16 (d.f0 12758 163) (d.f1 12758 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12758 : ℝ) ^ 8 * (mA 12758 : ℝ) ^ 8 *
        ((((4530792953 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4530792953 / 1000000000000000000)) * ((302309831 / 200000000000000000)) * (126 / 100) +
          2 * (((302309831 / 200000000000000000)) ^ 2 + 2 * ((4530792953 / 1000000000000000000)) * ((363301381 / 1000000000000000000))) +
          6 * ((302309831 / 200000000000000000)) * ((363301381 / 1000000000000000000)) * (126 / 100) + 8 * ((363301381 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12758) *
          (32 * (((4530792953 / 1000000000000000000) : ℝ) + (302309831 / 200000000000000000) + (363301381 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12758 : ℝ) ^ 16 *
      (d.w0 12758 163 + d.w1 12758 163 * √(π / 2) + 2 * d.w2 12758 163 +
        energyR16 12758 * radiusPolynomialRoot16 (d.w0 12758 163) (d.w1 12758 163)
          (d.w2 12758 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12758 : ℝ) ^ 16 *
        (((452077379 / 25000000000000000000) : ℝ) + ((32164441 / 2500000000000000000)) * (126 / 100) + 2 * ((23504149 / 5000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12758) *
          (32 * (((452077379 / 25000000000000000000) : ℝ) + (32164441 / 2500000000000000000) + (23504149 / 5000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12758

/-! A coarse bound on the actual paper statistics constant at dimension 12759. -/
namespace BstLean.Part266.Row12759
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12757 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12757 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12757 128 ≤ (13011 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13011 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12759) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12759 : ℕ))
    (by norm_num : (12759 : ℕ) ≤ 16384)
  have ht : paperTail256 12759 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12759 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12759 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12759 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12759 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12759 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12757 128 * √(2 / (12759 : ℝ)) *
      (√(12759 : ℝ) + paperT0 12759 + paperTail256 12759) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12759 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12759 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12759 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12757 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12757 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12759 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12759

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12759
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12759 (61 / 100) 163 (17 / (100 * 12759)) (26 / (10 * 12759)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12759 (61 / 100) 163 (17 / (100 * 12759)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (18798707 / 4000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1473368389 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4929409113 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12759 / 12759 * (61 / 100)) ^ 4 * inverseRadius8 (12759 - 1) /
            envelopeGap 12759 (61 / 100) 163 (17 / (100 * 12759)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12759

namespace BstLean.Part266.Row12759
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12759 163 ≤ (4529904997 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12759 163 ≤ (188906617 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (36323019 / 100000000000000000)
  w0 : (tableEnvelope C).w0 12759 163 ≤ (1807884303 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12759 163 ≤ (643137559 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12759 163 ≤ (469972451 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (18798707 / 4000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (18798707 / 4000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1473368389 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4929409113 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((730039 / 200000000) : ℝ) ≤ √(17 / (100 * 12759) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12759) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1083936893 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4798060137 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12759) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12759) ≤ (110840471 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12759) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12759 * (163 : ℝ) ^ 2 + 26 / (10 * 12759) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12759) : ℝ)) (tA 12759 * 163 ^ 2 + 26 / (10 * 12759)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((730039 / 200000000))) * ((18798707 / 4000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((730039 / 200000000)) ^ 3) * ((1473368389 / 1000000000000000000000000))) + ((4929409113 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((730039 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12759) : ℝ)) d.D d.V d.P (√(tA 12759) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((730039 / 200000000)) ^ 2 * (((1083936893 / 500000000000000)) * ((4798060137 / 125000000000000000)))) + ((4929409113 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12759) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((730039 / 200000000)) * ((18798707 / 4000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12759) : ℝ)) (tA 12759 * 163 ^ 2 + 26 / (10 * 12759)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((18798707 / 4000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((730039 / 200000000)) ^ 2) * ((1473368389 / 1000000000000000000000000)) + ((4929409113 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12759) : ℝ)) (√(26 / (10 * 12759) : ℝ)) d.D d.V d.P (√(tA 12759) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((730039 / 200000000)) * (((1083936893 / 500000000000000)) * ((4798060137 / 125000000000000000))) + ((4929409113 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12759) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((18798707 / 4000000000000000000) : ℝ) + ((4929409113 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12759

namespace BstLean.Part266.Row12759
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12759 163 ∧
    0 ≤ (tableEnvelope C).f1 12759 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12759 163 ∧
    0 ≤ (tableEnvelope C).w1 12759 163 ∧ 0 ≤ (tableEnvelope C).w2 12759 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12759 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12759 163 ∧ 0 ≤ d.f1 12759 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12759 163 ∧ 0 ≤ d.w1 12759 163 ∧ 0 ≤ d.w2 12759 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12759 ≤ 2 * (228 / 100 : ℝ) / 12759 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12759 ≤ 2 * (370 / 100 : ℝ) / 12759 := by
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
    (completeRAData (tableEnvelope C) 12759 163).locationBound 12759 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12759 163).energyBound 12759 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12759 163) (d.f1 12759 163) d.f2 ≤
      32 * (((4529904997 / 1000000000000000000) : ℝ) + (188906617 / 125000000000000000) + (36323019 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12759 163) (d.w1 12759 163)
      (d.w2 12759 163) ≤
      32 * (((1807884303 / 100000000000000000000) : ℝ) + (643137559 / 50000000000000000000) + (469972451 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12759 163) (d.f1 12759 163) d.f2 ≤
      ((4529904997 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4529904997 / 1000000000000000000)) * ((188906617 / 125000000000000000)) * (126 / 100) +
      2 * (((188906617 / 125000000000000000)) ^ 2 + 2 * ((4529904997 / 1000000000000000000)) * ((36323019 / 100000000000000000))) +
      6 * ((188906617 / 125000000000000000)) * ((36323019 / 100000000000000000)) * (126 / 100) + 8 * ((36323019 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12759 163) (d.f1 12759 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12759 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12759 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12759 163) (d.f1 12759 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12759 163) (d.w1 12759 163) (d.w2 12759 163)
  have hwexpr0 : 0 ≤ d.w0 12759 163 + d.w1 12759 163 * √(π / 2) +
      2 * d.w2 12759 163 + energyR16 12759 *
      radiusPolynomialRoot16 (d.w0 12759 163) (d.w1 12759 163) (d.w2 12759 163) := by
    positivity
  constructor
  · change (12759 : ℝ) ^ 8 * (mA 12759 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12759 163) (d.f1 12759 163) d.f2 + locationR16 12759 *
        radiusPolynomialRoot16 (d.f0 12759 163) (d.f1 12759 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12759 : ℝ) ^ 8 * (mA 12759 : ℝ) ^ 8 *
        ((((4529904997 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4529904997 / 1000000000000000000)) * ((188906617 / 125000000000000000)) * (126 / 100) +
          2 * (((188906617 / 125000000000000000)) ^ 2 + 2 * ((4529904997 / 1000000000000000000)) * ((36323019 / 100000000000000000))) +
          6 * ((188906617 / 125000000000000000)) * ((36323019 / 100000000000000000)) * (126 / 100) + 8 * ((36323019 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12759) *
          (32 * (((4529904997 / 1000000000000000000) : ℝ) + (188906617 / 125000000000000000) + (36323019 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12759 : ℝ) ^ 16 *
      (d.w0 12759 163 + d.w1 12759 163 * √(π / 2) + 2 * d.w2 12759 163 +
        energyR16 12759 * radiusPolynomialRoot16 (d.w0 12759 163) (d.w1 12759 163)
          (d.w2 12759 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12759 : ℝ) ^ 16 *
        (((1807884303 / 100000000000000000000) : ℝ) + ((643137559 / 50000000000000000000)) * (126 / 100) + 2 * ((469972451 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12759) *
          (32 * (((1807884303 / 100000000000000000000) : ℝ) + (643137559 / 50000000000000000000) + (469972451 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12759

/-! A coarse bound on the actual paper statistics constant at dimension 12760. -/
namespace BstLean.Part266.Row12760
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12758 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12758 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12758 128 ≤ (13012 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13012 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12760) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12760 : ℕ))
    (by norm_num : (12760 : ℕ) ≤ 16384)
  have ht : paperTail256 12760 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12760 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12760 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12760 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12760 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12760 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12758 128 * √(2 / (12760 : ℝ)) *
      (√(12760 : ℝ) + paperT0 12760 + paperTail256 12760) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12760 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12760 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12760 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12758 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12758 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12760 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12760

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12760
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12760 (61 / 100) 163 (17 / (100 * 12760)) (26 / (10 * 12760)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12760 (61 / 100) 163 (17 / (100 * 12760)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (14683037 / 3125000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (736453277 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4926289613 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12760 / 12760 * (61 / 100)) ^ 4 * inverseRadius8 (12760 - 1) /
            envelopeGap 12760 (61 / 100) 163 (17 / (100 * 12760)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12760

namespace BstLean.Part266.Row12760
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12760 163 ≤ (905803469 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12760 163 ≤ (755478407 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (18157951 / 50000000000000000)
  w0 : (tableEnvelope C).w0 12760 163 ≤ (1807459237 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12760 163 ≤ (1285972697 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12760 163 ≤ (469861957 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (14683037 / 3125000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (14683037 / 3125000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (736453277 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4926289613 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((912513 / 250000000) : ℝ) ≤ √(17 / (100 * 12760) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12760) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1083809467 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38378464717 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12760) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12760) ≤ (13853973 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12760) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12760 * (163 : ℝ) ^ 2 + 26 / (10 * 12760) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12760) : ℝ)) (tA 12760 * 163 ^ 2 + 26 / (10 * 12760)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((912513 / 250000000))) * ((14683037 / 3125000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((912513 / 250000000)) ^ 3) * ((736453277 / 500000000000000000000000))) + ((4926289613 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((912513 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12760) : ℝ)) d.D d.V d.P (√(tA 12760) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((912513 / 250000000)) ^ 2 * (((1083809467 / 500000000000000)) * ((38378464717 / 1000000000000000000)))) + ((4926289613 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12760) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((912513 / 250000000)) * ((14683037 / 3125000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12760) : ℝ)) (tA 12760 * 163 ^ 2 + 26 / (10 * 12760)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((14683037 / 3125000000000000000) : ℝ) + (24198 / 100000) / (2 * ((912513 / 250000000)) ^ 2) * ((736453277 / 500000000000000000000000)) + ((4926289613 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12760) : ℝ)) (√(26 / (10 * 12760) : ℝ)) d.D d.V d.P (√(tA 12760) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((912513 / 250000000)) * (((1083809467 / 500000000000000)) * ((38378464717 / 1000000000000000000))) + ((4926289613 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12760) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((14683037 / 3125000000000000000) : ℝ) + ((4926289613 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12760

namespace BstLean.Part266.Row12760
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12760 163 ∧
    0 ≤ (tableEnvelope C).f1 12760 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12760 163 ∧
    0 ≤ (tableEnvelope C).w1 12760 163 ∧ 0 ≤ (tableEnvelope C).w2 12760 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12760 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12760 163 ∧ 0 ≤ d.f1 12760 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12760 163 ∧ 0 ≤ d.w1 12760 163 ∧ 0 ≤ d.w2 12760 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12760 ≤ 2 * (228 / 100 : ℝ) / 12760 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12760 ≤ 2 * (370 / 100 : ℝ) / 12760 := by
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
    (completeRAData (tableEnvelope C) 12760 163).locationBound 12760 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12760 163).energyBound 12760 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12760 163) (d.f1 12760 163) d.f2 ≤
      32 * (((905803469 / 200000000000000000) : ℝ) + (755478407 / 500000000000000000) + (18157951 / 50000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12760 163) (d.w1 12760 163)
      (d.w2 12760 163) ≤
      32 * (((1807459237 / 100000000000000000000) : ℝ) + (1285972697 / 100000000000000000000) + (469861957 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12760 163) (d.f1 12760 163) d.f2 ≤
      ((905803469 / 200000000000000000) : ℝ) ^ 2 + 2 * ((905803469 / 200000000000000000)) * ((755478407 / 500000000000000000)) * (126 / 100) +
      2 * (((755478407 / 500000000000000000)) ^ 2 + 2 * ((905803469 / 200000000000000000)) * ((18157951 / 50000000000000000))) +
      6 * ((755478407 / 500000000000000000)) * ((18157951 / 50000000000000000)) * (126 / 100) + 8 * ((18157951 / 50000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12760 163) (d.f1 12760 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12760 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12760 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12760 163) (d.f1 12760 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12760 163) (d.w1 12760 163) (d.w2 12760 163)
  have hwexpr0 : 0 ≤ d.w0 12760 163 + d.w1 12760 163 * √(π / 2) +
      2 * d.w2 12760 163 + energyR16 12760 *
      radiusPolynomialRoot16 (d.w0 12760 163) (d.w1 12760 163) (d.w2 12760 163) := by
    positivity
  constructor
  · change (12760 : ℝ) ^ 8 * (mA 12760 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12760 163) (d.f1 12760 163) d.f2 + locationR16 12760 *
        radiusPolynomialRoot16 (d.f0 12760 163) (d.f1 12760 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12760 : ℝ) ^ 8 * (mA 12760 : ℝ) ^ 8 *
        ((((905803469 / 200000000000000000) : ℝ) ^ 2 + 2 * ((905803469 / 200000000000000000)) * ((755478407 / 500000000000000000)) * (126 / 100) +
          2 * (((755478407 / 500000000000000000)) ^ 2 + 2 * ((905803469 / 200000000000000000)) * ((18157951 / 50000000000000000))) +
          6 * ((755478407 / 500000000000000000)) * ((18157951 / 50000000000000000)) * (126 / 100) + 8 * ((18157951 / 50000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12760) *
          (32 * (((905803469 / 200000000000000000) : ℝ) + (755478407 / 500000000000000000) + (18157951 / 50000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12760 : ℝ) ^ 16 *
      (d.w0 12760 163 + d.w1 12760 163 * √(π / 2) + 2 * d.w2 12760 163 +
        energyR16 12760 * radiusPolynomialRoot16 (d.w0 12760 163) (d.w1 12760 163)
          (d.w2 12760 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12760 : ℝ) ^ 16 *
        (((1807459237 / 100000000000000000000) : ℝ) + ((1285972697 / 100000000000000000000)) * (126 / 100) + 2 * ((469861957 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12760) *
          (32 * (((1807459237 / 100000000000000000000) : ℝ) + (1285972697 / 100000000000000000000) + (469861957 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12760

/-! A coarse bound on the actual paper statistics constant at dimension 12761. -/
namespace BstLean.Part266.Row12761
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12759 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12759 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12759 128 ≤ (13013 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13013 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12761) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12761 : ℕ))
    (by norm_num : (12761 : ℕ) ≤ 16384)
  have ht : paperTail256 12761 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12761 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12761 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12761 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12761 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12761 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12759 128 * √(2 / (12761 : ℝ)) *
      (√(12761 : ℝ) + paperT0 12761 + paperTail256 12761) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12761 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12761 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12761 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12759 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12759 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12761 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12761

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12761
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12761 (61 / 100) 163 (17 / (100 * 12761)) (26 / (10 * 12761)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12761 (61 / 100) 163 (17 / (100 * 12761)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (58718341 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (14724449 / 10000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (307698271 / 62500000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12761 / 12761 * (61 / 100)) ^ 4 * inverseRadius8 (12761 - 1) /
            envelopeGap 12761 (61 / 100) 163 (17 / (100 * 12761)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12761

namespace BstLean.Part266.Row12761
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12761 163 ≤ (4528129997 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12761 163 ≤ (1510660787 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (177289 / 488281250000000)
  w0 : (tableEnvelope C).w0 12761 163 ≤ (451758579 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12761 163 ≤ (642835189 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12761 163 ≤ (234875749 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (58718341 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (58718341 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (14724449 / 10000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (307698271 / 62500000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3649909 / 1000000000) : ℝ) ≤ √(17 / (100 * 12761) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12761) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (541841033 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38372449753 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12761) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12761) ≤ (110823099 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12761) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12761 * (163 : ℝ) ^ 2 + 26 / (10 * 12761) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12761) : ℝ)) (tA 12761 * 163 ^ 2 + 26 / (10 * 12761)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3649909 / 1000000000))) * ((58718341 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3649909 / 1000000000)) ^ 3) * ((14724449 / 10000000000000000000000))) + ((307698271 / 62500000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3649909 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12761) : ℝ)) d.D d.V d.P (√(tA 12761) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3649909 / 1000000000)) ^ 2 * (((541841033 / 250000000000000)) * ((38372449753 / 1000000000000000000)))) + ((307698271 / 62500000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12761) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3649909 / 1000000000)) * ((58718341 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12761) : ℝ)) (tA 12761 * 163 ^ 2 + 26 / (10 * 12761)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((58718341 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3649909 / 1000000000)) ^ 2) * ((14724449 / 10000000000000000000000)) + ((307698271 / 62500000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12761) : ℝ)) (√(26 / (10 * 12761) : ℝ)) d.D d.V d.P (√(tA 12761) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3649909 / 1000000000)) * (((541841033 / 250000000000000)) * ((38372449753 / 1000000000000000000))) + ((307698271 / 62500000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12761) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((58718341 / 12500000000000000000) : ℝ) + ((307698271 / 62500000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12761

namespace BstLean.Part266.Row12761
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12761 163 ∧
    0 ≤ (tableEnvelope C).f1 12761 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12761 163 ∧
    0 ≤ (tableEnvelope C).w1 12761 163 ∧ 0 ≤ (tableEnvelope C).w2 12761 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12761 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12761 163 ∧ 0 ≤ d.f1 12761 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12761 163 ∧ 0 ≤ d.w1 12761 163 ∧ 0 ≤ d.w2 12761 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12761 ≤ 2 * (228 / 100 : ℝ) / 12761 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12761 ≤ 2 * (370 / 100 : ℝ) / 12761 := by
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
    (completeRAData (tableEnvelope C) 12761 163).locationBound 12761 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12761 163).energyBound 12761 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12761 163) (d.f1 12761 163) d.f2 ≤
      32 * (((4528129997 / 1000000000000000000) : ℝ) + (1510660787 / 1000000000000000000) + (177289 / 488281250000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12761 163) (d.w1 12761 163)
      (d.w2 12761 163) ≤
      32 * (((451758579 / 25000000000000000000) : ℝ) + (642835189 / 50000000000000000000) + (234875749 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12761 163) (d.f1 12761 163) d.f2 ≤
      ((4528129997 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4528129997 / 1000000000000000000)) * ((1510660787 / 1000000000000000000)) * (126 / 100) +
      2 * (((1510660787 / 1000000000000000000)) ^ 2 + 2 * ((4528129997 / 1000000000000000000)) * ((177289 / 488281250000000))) +
      6 * ((1510660787 / 1000000000000000000)) * ((177289 / 488281250000000)) * (126 / 100) + 8 * ((177289 / 488281250000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12761 163) (d.f1 12761 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12761 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12761 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12761 163) (d.f1 12761 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12761 163) (d.w1 12761 163) (d.w2 12761 163)
  have hwexpr0 : 0 ≤ d.w0 12761 163 + d.w1 12761 163 * √(π / 2) +
      2 * d.w2 12761 163 + energyR16 12761 *
      radiusPolynomialRoot16 (d.w0 12761 163) (d.w1 12761 163) (d.w2 12761 163) := by
    positivity
  constructor
  · change (12761 : ℝ) ^ 8 * (mA 12761 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12761 163) (d.f1 12761 163) d.f2 + locationR16 12761 *
        radiusPolynomialRoot16 (d.f0 12761 163) (d.f1 12761 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12761 : ℝ) ^ 8 * (mA 12761 : ℝ) ^ 8 *
        ((((4528129997 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4528129997 / 1000000000000000000)) * ((1510660787 / 1000000000000000000)) * (126 / 100) +
          2 * (((1510660787 / 1000000000000000000)) ^ 2 + 2 * ((4528129997 / 1000000000000000000)) * ((177289 / 488281250000000))) +
          6 * ((1510660787 / 1000000000000000000)) * ((177289 / 488281250000000)) * (126 / 100) + 8 * ((177289 / 488281250000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12761) *
          (32 * (((4528129997 / 1000000000000000000) : ℝ) + (1510660787 / 1000000000000000000) + (177289 / 488281250000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12761 : ℝ) ^ 16 *
      (d.w0 12761 163 + d.w1 12761 163 * √(π / 2) + 2 * d.w2 12761 163 +
        energyR16 12761 * radiusPolynomialRoot16 (d.w0 12761 163) (d.w1 12761 163)
          (d.w2 12761 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12761 : ℝ) ^ 16 *
        (((451758579 / 25000000000000000000) : ℝ) + ((642835189 / 50000000000000000000)) * (126 / 100) + 2 * ((234875749 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12761) *
          (32 * (((451758579 / 25000000000000000000) : ℝ) + (642835189 / 50000000000000000000) + (234875749 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12761

/-! A coarse bound on the actual paper statistics constant at dimension 12762. -/
namespace BstLean.Part266.Row12762
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12760 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12760 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12760 128 ≤ (13014 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13014 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12762) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12762 : ℕ))
    (by norm_num : (12762 : ℕ) ≤ 16384)
  have ht : paperTail256 12762 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12762 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12762 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12762 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12762 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12762 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12760 128 * √(2 / (12762 : ℝ)) *
      (√(12762 : ℝ) + paperT0 12762 + paperTail256 12762) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12762 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12762 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12762 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12760 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12760 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12762 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12762

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12762
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12762 (61 / 100) 163 (17 / (100 * 12762)) (26 / (10 * 12762)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12762 (61 / 100) 163 (17 / (100 * 12762)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (234818153 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1471983427 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (15375179 / 3125000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12762 / 12762 * (61 / 100)) ^ 4 * inverseRadius8 (12762 - 1) /
            envelopeGap 12762 (61 / 100) 163 (17 / (100 * 12762)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12762

namespace BstLean.Part266.Row12762
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12762 163 ≤ (565905369 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12762 163 ≤ (755182427 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (72603349 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12762 163 ≤ (90330477 / 5000000000000000000)
  w1 : (tableEnvelope C).w1 12762 163 ≤ (642684079 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12762 163 ≤ (469641073 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (234818153 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (234818153 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1471983427 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (15375179 / 3125000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1824883 / 500000000) : ℝ) ≤ √(17 / (100 * 12762) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12762) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2167109379 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7673287241 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12762) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12762) ≤ (22162883 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12762) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12762 * (163 : ℝ) ^ 2 + 26 / (10 * 12762) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12762) : ℝ)) (tA 12762 * 163 ^ 2 + 26 / (10 * 12762)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1824883 / 500000000))) * ((234818153 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1824883 / 500000000)) ^ 3) * ((1471983427 / 1000000000000000000000000))) + ((15375179 / 3125000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1824883 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12762) : ℝ)) d.D d.V d.P (√(tA 12762) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1824883 / 500000000)) ^ 2 * (((2167109379 / 1000000000000000)) * ((7673287241 / 200000000000000000)))) + ((15375179 / 3125000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12762) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1824883 / 500000000)) * ((234818153 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12762) : ℝ)) (tA 12762 * 163 ^ 2 + 26 / (10 * 12762)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((234818153 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1824883 / 500000000)) ^ 2) * ((1471983427 / 1000000000000000000000000)) + ((15375179 / 3125000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12762) : ℝ)) (√(26 / (10 * 12762) : ℝ)) d.D d.V d.P (√(tA 12762) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1824883 / 500000000)) * (((2167109379 / 1000000000000000)) * ((7673287241 / 200000000000000000))) + ((15375179 / 3125000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12762) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((234818153 / 50000000000000000000) : ℝ) + ((15375179 / 3125000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12762

namespace BstLean.Part266.Row12762
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12762 163 ∧
    0 ≤ (tableEnvelope C).f1 12762 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12762 163 ∧
    0 ≤ (tableEnvelope C).w1 12762 163 ∧ 0 ≤ (tableEnvelope C).w2 12762 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12762 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12762 163 ∧ 0 ≤ d.f1 12762 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12762 163 ∧ 0 ≤ d.w1 12762 163 ∧ 0 ≤ d.w2 12762 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12762 ≤ 2 * (228 / 100 : ℝ) / 12762 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12762 ≤ 2 * (370 / 100 : ℝ) / 12762 := by
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
    (completeRAData (tableEnvelope C) 12762 163).locationBound 12762 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12762 163).energyBound 12762 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12762 163) (d.f1 12762 163) d.f2 ≤
      32 * (((565905369 / 125000000000000000) : ℝ) + (755182427 / 500000000000000000) + (72603349 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12762 163) (d.w1 12762 163)
      (d.w2 12762 163) ≤
      32 * (((90330477 / 5000000000000000000) : ℝ) + (642684079 / 50000000000000000000) + (469641073 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12762 163) (d.f1 12762 163) d.f2 ≤
      ((565905369 / 125000000000000000) : ℝ) ^ 2 + 2 * ((565905369 / 125000000000000000)) * ((755182427 / 500000000000000000)) * (126 / 100) +
      2 * (((755182427 / 500000000000000000)) ^ 2 + 2 * ((565905369 / 125000000000000000)) * ((72603349 / 200000000000000000))) +
      6 * ((755182427 / 500000000000000000)) * ((72603349 / 200000000000000000)) * (126 / 100) + 8 * ((72603349 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12762 163) (d.f1 12762 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12762 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12762 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12762 163) (d.f1 12762 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12762 163) (d.w1 12762 163) (d.w2 12762 163)
  have hwexpr0 : 0 ≤ d.w0 12762 163 + d.w1 12762 163 * √(π / 2) +
      2 * d.w2 12762 163 + energyR16 12762 *
      radiusPolynomialRoot16 (d.w0 12762 163) (d.w1 12762 163) (d.w2 12762 163) := by
    positivity
  constructor
  · change (12762 : ℝ) ^ 8 * (mA 12762 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12762 163) (d.f1 12762 163) d.f2 + locationR16 12762 *
        radiusPolynomialRoot16 (d.f0 12762 163) (d.f1 12762 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12762 : ℝ) ^ 8 * (mA 12762 : ℝ) ^ 8 *
        ((((565905369 / 125000000000000000) : ℝ) ^ 2 + 2 * ((565905369 / 125000000000000000)) * ((755182427 / 500000000000000000)) * (126 / 100) +
          2 * (((755182427 / 500000000000000000)) ^ 2 + 2 * ((565905369 / 125000000000000000)) * ((72603349 / 200000000000000000))) +
          6 * ((755182427 / 500000000000000000)) * ((72603349 / 200000000000000000)) * (126 / 100) + 8 * ((72603349 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12762) *
          (32 * (((565905369 / 125000000000000000) : ℝ) + (755182427 / 500000000000000000) + (72603349 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12762 : ℝ) ^ 16 *
      (d.w0 12762 163 + d.w1 12762 163 * √(π / 2) + 2 * d.w2 12762 163 +
        energyR16 12762 * radiusPolynomialRoot16 (d.w0 12762 163) (d.w1 12762 163)
          (d.w2 12762 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12762 : ℝ) ^ 16 *
        (((90330477 / 5000000000000000000) : ℝ) + ((642684079 / 50000000000000000000)) * (126 / 100) + 2 * ((469641073 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12762) *
          (32 * (((90330477 / 5000000000000000000) : ℝ) + (642684079 / 50000000000000000000) + (469641073 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12762

/-! A coarse bound on the actual paper statistics constant at dimension 12763. -/
namespace BstLean.Part266.Row12763
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12761 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12761 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12761 128 ≤ (13015 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13015 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12763) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12763 : ℕ))
    (by norm_num : (12763 : ℕ) ≤ 16384)
  have ht : paperTail256 12763 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12763 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12763 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12763 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12763 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12763 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12761 128 * √(2 / (12763 : ℝ)) *
      (√(12763 : ℝ) + paperT0 12763 + paperTail256 12763) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12763 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12763 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12763 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12761 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12761 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12763 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12763

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12763
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12763 (61 / 100) 163 (17 / (100 * 12763)) (26 / (10 * 12763)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12763 (61 / 100) 163 (17 / (100 * 12763)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (469525919 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (294304427 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1229236111 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12763 / 12763 * (61 / 100)) ^ 4 * inverseRadius8 (12763 - 1) /
            envelopeGap 12763 (61 / 100) 163 (17 / (100 * 12763)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12763

namespace BstLean.Part266.Row12763
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12763 163 ≤ (1131589053 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12763 163 ≤ (1510069017 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (362945639 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12763 163 ≤ (1806184911 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12763 163 ≤ (32126651 / 2500000000000000000)
  w2 : (tableEnvelope C).w2 12763 163 ≤ (234765341 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (469525919 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (469525919 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (294304427 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1229236111 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3649623 / 1000000000) : ℝ) ≤ √(17 / (100 * 12763) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12763) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2166854677 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38360424073 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12763) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12763) ≤ (110805733 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12763) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12763 * (163 : ℝ) ^ 2 + 26 / (10 * 12763) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12763) : ℝ)) (tA 12763 * 163 ^ 2 + 26 / (10 * 12763)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3649623 / 1000000000))) * ((469525919 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3649623 / 1000000000)) ^ 3) * ((294304427 / 200000000000000000000000))) + ((1229236111 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3649623 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12763) : ℝ)) d.D d.V d.P (√(tA 12763) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3649623 / 1000000000)) ^ 2 * (((2166854677 / 1000000000000000)) * ((38360424073 / 1000000000000000000)))) + ((1229236111 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12763) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3649623 / 1000000000)) * ((469525919 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12763) : ℝ)) (tA 12763 * 163 ^ 2 + 26 / (10 * 12763)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((469525919 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3649623 / 1000000000)) ^ 2) * ((294304427 / 200000000000000000000000)) + ((1229236111 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12763) : ℝ)) (√(26 / (10 * 12763) : ℝ)) d.D d.V d.P (√(tA 12763) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3649623 / 1000000000)) * (((2166854677 / 1000000000000000)) * ((38360424073 / 1000000000000000000))) + ((1229236111 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12763) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((469525919 / 100000000000000000000) : ℝ) + ((1229236111 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12763

namespace BstLean.Part266.Row12763
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12763 163 ∧
    0 ≤ (tableEnvelope C).f1 12763 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12763 163 ∧
    0 ≤ (tableEnvelope C).w1 12763 163 ∧ 0 ≤ (tableEnvelope C).w2 12763 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12763 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12763 163 ∧ 0 ≤ d.f1 12763 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12763 163 ∧ 0 ≤ d.w1 12763 163 ∧ 0 ≤ d.w2 12763 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12763 ≤ 2 * (228 / 100 : ℝ) / 12763 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12763 ≤ 2 * (370 / 100 : ℝ) / 12763 := by
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
    (completeRAData (tableEnvelope C) 12763 163).locationBound 12763 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12763 163).energyBound 12763 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12763 163) (d.f1 12763 163) d.f2 ≤
      32 * (((1131589053 / 250000000000000000) : ℝ) + (1510069017 / 1000000000000000000) + (362945639 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12763 163) (d.w1 12763 163)
      (d.w2 12763 163) ≤
      32 * (((1806184911 / 100000000000000000000) : ℝ) + (32126651 / 2500000000000000000) + (234765341 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12763 163) (d.f1 12763 163) d.f2 ≤
      ((1131589053 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1131589053 / 250000000000000000)) * ((1510069017 / 1000000000000000000)) * (126 / 100) +
      2 * (((1510069017 / 1000000000000000000)) ^ 2 + 2 * ((1131589053 / 250000000000000000)) * ((362945639 / 1000000000000000000))) +
      6 * ((1510069017 / 1000000000000000000)) * ((362945639 / 1000000000000000000)) * (126 / 100) + 8 * ((362945639 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12763 163) (d.f1 12763 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12763 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12763 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12763 163) (d.f1 12763 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12763 163) (d.w1 12763 163) (d.w2 12763 163)
  have hwexpr0 : 0 ≤ d.w0 12763 163 + d.w1 12763 163 * √(π / 2) +
      2 * d.w2 12763 163 + energyR16 12763 *
      radiusPolynomialRoot16 (d.w0 12763 163) (d.w1 12763 163) (d.w2 12763 163) := by
    positivity
  constructor
  · change (12763 : ℝ) ^ 8 * (mA 12763 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12763 163) (d.f1 12763 163) d.f2 + locationR16 12763 *
        radiusPolynomialRoot16 (d.f0 12763 163) (d.f1 12763 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12763 : ℝ) ^ 8 * (mA 12763 : ℝ) ^ 8 *
        ((((1131589053 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1131589053 / 250000000000000000)) * ((1510069017 / 1000000000000000000)) * (126 / 100) +
          2 * (((1510069017 / 1000000000000000000)) ^ 2 + 2 * ((1131589053 / 250000000000000000)) * ((362945639 / 1000000000000000000))) +
          6 * ((1510069017 / 1000000000000000000)) * ((362945639 / 1000000000000000000)) * (126 / 100) + 8 * ((362945639 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12763) *
          (32 * (((1131589053 / 250000000000000000) : ℝ) + (1510069017 / 1000000000000000000) + (362945639 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12763 : ℝ) ^ 16 *
      (d.w0 12763 163 + d.w1 12763 163 * √(π / 2) + 2 * d.w2 12763 163 +
        energyR16 12763 * radiusPolynomialRoot16 (d.w0 12763 163) (d.w1 12763 163)
          (d.w2 12763 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12763 : ℝ) ^ 16 *
        (((1806184911 / 100000000000000000000) : ℝ) + ((32126651 / 2500000000000000000)) * (126 / 100) + 2 * ((234765341 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12763) *
          (32 * (((1806184911 / 100000000000000000000) : ℝ) + (32126651 / 2500000000000000000) + (234765341 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12763

/-! A coarse bound on the actual paper statistics constant at dimension 12764. -/
namespace BstLean.Part266.Row12764
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12762 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12762 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12762 128 ≤ (13016 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13016 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12764) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12764 : ℕ))
    (by norm_num : (12764 : ℕ) ≤ 16384)
  have ht : paperTail256 12764 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12764 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12764 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12764 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12764 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12764 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12762 128 * √(2 / (12764 : ℝ)) *
      (√(12764 : ℝ) + paperT0 12764 + paperTail256 12764) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12764 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12764 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12764 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12762 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12762 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12764 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12764

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12764
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12764 (61 / 100) 163 (17 / (100 * 12764)) (26 / (10 * 12764)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12764 (61 / 100) 163 (17 / (100 * 12764)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (234707783 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (45970657 / 31250000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2456916913 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12764 / 12764 * (61 / 100)) ^ 4 * inverseRadius8 (12764 - 1) /
            envelopeGap 12764 (61 / 100) 163 (17 / (100 * 12764)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12764

namespace BstLean.Part266.Row12764
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12764 163 ≤ (282841861 / 62500000000000000)
  f1 : (tableEnvelope C).f1 12764 163 ≤ (60390931 / 40000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (181437277 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12764 163 ≤ (902880213 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12764 163 ≤ (642382011 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12764 163 ≤ (234710163 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (234707783 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (234707783 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (45970657 / 31250000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2456916913 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((91237 / 25000000) : ℝ) ≤ √(17 / (100 * 12764) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12764) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (270825003 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19177206679 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12764) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12764) ≤ (27699263 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12764) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12764 * (163 : ℝ) ^ 2 + 26 / (10 * 12764) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12764) : ℝ)) (tA 12764 * 163 ^ 2 + 26 / (10 * 12764)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((91237 / 25000000))) * ((234707783 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((91237 / 25000000)) ^ 3) * ((45970657 / 31250000000000000000000))) + ((2456916913 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((91237 / 25000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12764) : ℝ)) d.D d.V d.P (√(tA 12764) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((91237 / 25000000)) ^ 2 * (((270825003 / 125000000000000)) * ((19177206679 / 500000000000000000)))) + ((2456916913 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12764) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((91237 / 25000000)) * ((234707783 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12764) : ℝ)) (tA 12764 * 163 ^ 2 + 26 / (10 * 12764)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((234707783 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((91237 / 25000000)) ^ 2) * ((45970657 / 31250000000000000000000)) + ((2456916913 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12764) : ℝ)) (√(26 / (10 * 12764) : ℝ)) d.D d.V d.P (√(tA 12764) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((91237 / 25000000)) * (((270825003 / 125000000000000)) * ((19177206679 / 500000000000000000))) + ((2456916913 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12764) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((234707783 / 50000000000000000000) : ℝ) + ((2456916913 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12764

namespace BstLean.Part266.Row12764
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12764 163 ∧
    0 ≤ (tableEnvelope C).f1 12764 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12764 163 ∧
    0 ≤ (tableEnvelope C).w1 12764 163 ∧ 0 ≤ (tableEnvelope C).w2 12764 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12764 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12764 163 ∧ 0 ≤ d.f1 12764 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12764 163 ∧ 0 ≤ d.w1 12764 163 ∧ 0 ≤ d.w2 12764 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12764 ≤ 2 * (228 / 100 : ℝ) / 12764 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12764 ≤ 2 * (370 / 100 : ℝ) / 12764 := by
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
    (completeRAData (tableEnvelope C) 12764 163).locationBound 12764 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12764 163).energyBound 12764 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12764 163) (d.f1 12764 163) d.f2 ≤
      32 * (((282841861 / 62500000000000000) : ℝ) + (60390931 / 40000000000000000) + (181437277 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12764 163) (d.w1 12764 163)
      (d.w2 12764 163) ≤
      32 * (((902880213 / 50000000000000000000) : ℝ) + (642382011 / 50000000000000000000) + (234710163 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12764 163) (d.f1 12764 163) d.f2 ≤
      ((282841861 / 62500000000000000) : ℝ) ^ 2 + 2 * ((282841861 / 62500000000000000)) * ((60390931 / 40000000000000000)) * (126 / 100) +
      2 * (((60390931 / 40000000000000000)) ^ 2 + 2 * ((282841861 / 62500000000000000)) * ((181437277 / 500000000000000000))) +
      6 * ((60390931 / 40000000000000000)) * ((181437277 / 500000000000000000)) * (126 / 100) + 8 * ((181437277 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12764 163) (d.f1 12764 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12764 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12764 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12764 163) (d.f1 12764 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12764 163) (d.w1 12764 163) (d.w2 12764 163)
  have hwexpr0 : 0 ≤ d.w0 12764 163 + d.w1 12764 163 * √(π / 2) +
      2 * d.w2 12764 163 + energyR16 12764 *
      radiusPolynomialRoot16 (d.w0 12764 163) (d.w1 12764 163) (d.w2 12764 163) := by
    positivity
  constructor
  · change (12764 : ℝ) ^ 8 * (mA 12764 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12764 163) (d.f1 12764 163) d.f2 + locationR16 12764 *
        radiusPolynomialRoot16 (d.f0 12764 163) (d.f1 12764 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12764 : ℝ) ^ 8 * (mA 12764 : ℝ) ^ 8 *
        ((((282841861 / 62500000000000000) : ℝ) ^ 2 + 2 * ((282841861 / 62500000000000000)) * ((60390931 / 40000000000000000)) * (126 / 100) +
          2 * (((60390931 / 40000000000000000)) ^ 2 + 2 * ((282841861 / 62500000000000000)) * ((181437277 / 500000000000000000))) +
          6 * ((60390931 / 40000000000000000)) * ((181437277 / 500000000000000000)) * (126 / 100) + 8 * ((181437277 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12764) *
          (32 * (((282841861 / 62500000000000000) : ℝ) + (60390931 / 40000000000000000) + (181437277 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12764 : ℝ) ^ 16 *
      (d.w0 12764 163 + d.w1 12764 163 * √(π / 2) + 2 * d.w2 12764 163 +
        energyR16 12764 * radiusPolynomialRoot16 (d.w0 12764 163) (d.w1 12764 163)
          (d.w2 12764 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12764 : ℝ) ^ 16 *
        (((902880213 / 50000000000000000000) : ℝ) + ((642382011 / 50000000000000000000)) * (126 / 100) + 2 * ((234710163 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12764) *
          (32 * (((902880213 / 50000000000000000000) : ℝ) + (642382011 / 50000000000000000000) + (234710163 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12764

/-! A coarse bound on the actual paper statistics constant at dimension 12765. -/
namespace BstLean.Part266.Row12765
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12763 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12763 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12763 128 ≤ (13017 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13017 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12765) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12765 : ℕ))
    (by norm_num : (12765 : ℕ) ≤ 16384)
  have ht : paperTail256 12765 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12765 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12765 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12765 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12765 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12765 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12763 128 * √(2 / (12765 : ℝ)) *
      (√(12765 : ℝ) + paperT0 12765 + paperTail256 12765) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12765 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12765 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12765 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12763 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12763 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12765 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12765

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12765
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12765 (61 / 100) 163 (17 / (100 * 12765)) (26 / (10 * 12765)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12765 (61 / 100) 163 (17 / (100 * 12765)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (14665789 / 3125000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1470600093 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4910725423 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12765 / 12765 * (61 / 100)) ^ 4 * inverseRadius8 (12765 - 1) /
            envelopeGap 12765 (61 / 100) 163 (17 / (100 * 12765)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12765

namespace BstLean.Part266.Row12765
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12765 163 ≤ (2262291821 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12765 163 ≤ (1509477627 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (36280349 / 100000000000000000)
  w0 : (tableEnvelope C).w0 12765 163 ≤ (1805336087 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12765 163 ≤ (160557763 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 12765 163 ≤ (93862001 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (14665789 / 3125000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (14665789 / 3125000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1470600093 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4910725423 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3649337 / 1000000000) : ℝ) ≤ √(17 / (100 * 12765) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12765) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2166345421 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (2396775253 / 62500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12765) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12765) ≤ (27697093 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12765) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12765 * (163 : ℝ) ^ 2 + 26 / (10 * 12765) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12765) : ℝ)) (tA 12765 * 163 ^ 2 + 26 / (10 * 12765)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3649337 / 1000000000))) * ((14665789 / 3125000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3649337 / 1000000000)) ^ 3) * ((1470600093 / 1000000000000000000000000))) + ((4910725423 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3649337 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12765) : ℝ)) d.D d.V d.P (√(tA 12765) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3649337 / 1000000000)) ^ 2 * (((2166345421 / 1000000000000000)) * ((2396775253 / 62500000000000000)))) + ((4910725423 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12765) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3649337 / 1000000000)) * ((14665789 / 3125000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12765) : ℝ)) (tA 12765 * 163 ^ 2 + 26 / (10 * 12765)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((14665789 / 3125000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3649337 / 1000000000)) ^ 2) * ((1470600093 / 1000000000000000000000000)) + ((4910725423 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12765) : ℝ)) (√(26 / (10 * 12765) : ℝ)) d.D d.V d.P (√(tA 12765) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3649337 / 1000000000)) * (((2166345421 / 1000000000000000)) * ((2396775253 / 62500000000000000))) + ((4910725423 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12765) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((14665789 / 3125000000000000000) : ℝ) + ((4910725423 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12765

namespace BstLean.Part266.Row12765
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12765 163 ∧
    0 ≤ (tableEnvelope C).f1 12765 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12765 163 ∧
    0 ≤ (tableEnvelope C).w1 12765 163 ∧ 0 ≤ (tableEnvelope C).w2 12765 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12765 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12765 163 ∧ 0 ≤ d.f1 12765 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12765 163 ∧ 0 ≤ d.w1 12765 163 ∧ 0 ≤ d.w2 12765 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12765 ≤ 2 * (228 / 100 : ℝ) / 12765 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12765 ≤ 2 * (370 / 100 : ℝ) / 12765 := by
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
    (completeRAData (tableEnvelope C) 12765 163).locationBound 12765 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12765 163).energyBound 12765 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12765 163) (d.f1 12765 163) d.f2 ≤
      32 * (((2262291821 / 500000000000000000) : ℝ) + (1509477627 / 1000000000000000000) + (36280349 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12765 163) (d.w1 12765 163)
      (d.w2 12765 163) ≤
      32 * (((1805336087 / 100000000000000000000) : ℝ) + (160557763 / 12500000000000000000) + (93862001 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12765 163) (d.f1 12765 163) d.f2 ≤
      ((2262291821 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2262291821 / 500000000000000000)) * ((1509477627 / 1000000000000000000)) * (126 / 100) +
      2 * (((1509477627 / 1000000000000000000)) ^ 2 + 2 * ((2262291821 / 500000000000000000)) * ((36280349 / 100000000000000000))) +
      6 * ((1509477627 / 1000000000000000000)) * ((36280349 / 100000000000000000)) * (126 / 100) + 8 * ((36280349 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12765 163) (d.f1 12765 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12765 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12765 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12765 163) (d.f1 12765 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12765 163) (d.w1 12765 163) (d.w2 12765 163)
  have hwexpr0 : 0 ≤ d.w0 12765 163 + d.w1 12765 163 * √(π / 2) +
      2 * d.w2 12765 163 + energyR16 12765 *
      radiusPolynomialRoot16 (d.w0 12765 163) (d.w1 12765 163) (d.w2 12765 163) := by
    positivity
  constructor
  · change (12765 : ℝ) ^ 8 * (mA 12765 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12765 163) (d.f1 12765 163) d.f2 + locationR16 12765 *
        radiusPolynomialRoot16 (d.f0 12765 163) (d.f1 12765 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12765 : ℝ) ^ 8 * (mA 12765 : ℝ) ^ 8 *
        ((((2262291821 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2262291821 / 500000000000000000)) * ((1509477627 / 1000000000000000000)) * (126 / 100) +
          2 * (((1509477627 / 1000000000000000000)) ^ 2 + 2 * ((2262291821 / 500000000000000000)) * ((36280349 / 100000000000000000))) +
          6 * ((1509477627 / 1000000000000000000)) * ((36280349 / 100000000000000000)) * (126 / 100) + 8 * ((36280349 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12765) *
          (32 * (((2262291821 / 500000000000000000) : ℝ) + (1509477627 / 1000000000000000000) + (36280349 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12765 : ℝ) ^ 16 *
      (d.w0 12765 163 + d.w1 12765 163 * √(π / 2) + 2 * d.w2 12765 163 +
        energyR16 12765 * radiusPolynomialRoot16 (d.w0 12765 163) (d.w1 12765 163)
          (d.w2 12765 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12765 : ℝ) ^ 16 *
        (((1805336087 / 100000000000000000000) : ℝ) + ((160557763 / 12500000000000000000)) * (126 / 100) + 2 * ((93862001 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12765) *
          (32 * (((1805336087 / 100000000000000000000) : ℝ) + (160557763 / 12500000000000000000) + (93862001 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12765

/-! A coarse bound on the actual paper statistics constant at dimension 12766. -/
namespace BstLean.Part266.Row12766
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12764 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12764 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12764 128 ≤ (13018 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13018 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12766) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12766 : ℕ))
    (by norm_num : (12766 : ℕ) ≤ 16384)
  have ht : paperTail256 12766 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12766 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12766 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12766 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12766 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12766 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12764 128 * √(2 / (12766 : ℝ)) *
      (√(12766 : ℝ) + paperT0 12766 + paperTail256 12766) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12766 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12766 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12766 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12764 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12764 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12766 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12766

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12766
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12766 (61 / 100) 163 (17 / (100 * 12766)) (26 / (10 * 12766)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12766 (61 / 100) 163 (17 / (100 * 12766)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (117298741 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (735069671 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (981523847 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12766 / 12766 * (61 / 100)) ^ 4 * inverseRadius8 (12766 - 1) /
            envelopeGap 12766 (61 / 100) 163 (17 / (100 * 12766)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12766

namespace BstLean.Part266.Row12766
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12766 163 ≤ (282731113 / 62500000000000000)
  f1 : (tableEnvelope C).f1 12766 163 ≤ (754591037 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (362732447 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12766 163 ≤ (451227973 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12766 163 ≤ (642080143 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12766 163 ≤ (234599859 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (117298741 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (117298741 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (735069671 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (981523847 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1824597 / 500000000) : ℝ) ≤ √(17 / (100 * 12766) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12766) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2166090867 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (2396399759 / 62500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12766) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12766) ≤ (55389847 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12766) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12766 * (163 : ℝ) ^ 2 + 26 / (10 * 12766) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12766) : ℝ)) (tA 12766 * 163 ^ 2 + 26 / (10 * 12766)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1824597 / 500000000))) * ((117298741 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1824597 / 500000000)) ^ 3) * ((735069671 / 500000000000000000000000))) + ((981523847 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1824597 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12766) : ℝ)) d.D d.V d.P (√(tA 12766) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1824597 / 500000000)) ^ 2 * (((2166090867 / 1000000000000000)) * ((2396399759 / 62500000000000000)))) + ((981523847 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12766) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1824597 / 500000000)) * ((117298741 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12766) : ℝ)) (tA 12766 * 163 ^ 2 + 26 / (10 * 12766)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((117298741 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1824597 / 500000000)) ^ 2) * ((735069671 / 500000000000000000000000)) + ((981523847 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12766) : ℝ)) (√(26 / (10 * 12766) : ℝ)) d.D d.V d.P (√(tA 12766) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1824597 / 500000000)) * (((2166090867 / 1000000000000000)) * ((2396399759 / 62500000000000000))) + ((981523847 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12766) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((117298741 / 25000000000000000000) : ℝ) + ((981523847 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12766

namespace BstLean.Part266.Row12766
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12766 163 ∧
    0 ≤ (tableEnvelope C).f1 12766 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12766 163 ∧
    0 ≤ (tableEnvelope C).w1 12766 163 ∧ 0 ≤ (tableEnvelope C).w2 12766 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12766 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12766 163 ∧ 0 ≤ d.f1 12766 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12766 163 ∧ 0 ≤ d.w1 12766 163 ∧ 0 ≤ d.w2 12766 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12766 ≤ 2 * (228 / 100 : ℝ) / 12766 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12766 ≤ 2 * (370 / 100 : ℝ) / 12766 := by
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
    (completeRAData (tableEnvelope C) 12766 163).locationBound 12766 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12766 163).energyBound 12766 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12766 163) (d.f1 12766 163) d.f2 ≤
      32 * (((282731113 / 62500000000000000) : ℝ) + (754591037 / 500000000000000000) + (362732447 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12766 163) (d.w1 12766 163)
      (d.w2 12766 163) ≤
      32 * (((451227973 / 25000000000000000000) : ℝ) + (642080143 / 50000000000000000000) + (234599859 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12766 163) (d.f1 12766 163) d.f2 ≤
      ((282731113 / 62500000000000000) : ℝ) ^ 2 + 2 * ((282731113 / 62500000000000000)) * ((754591037 / 500000000000000000)) * (126 / 100) +
      2 * (((754591037 / 500000000000000000)) ^ 2 + 2 * ((282731113 / 62500000000000000)) * ((362732447 / 1000000000000000000))) +
      6 * ((754591037 / 500000000000000000)) * ((362732447 / 1000000000000000000)) * (126 / 100) + 8 * ((362732447 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12766 163) (d.f1 12766 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12766 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12766 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12766 163) (d.f1 12766 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12766 163) (d.w1 12766 163) (d.w2 12766 163)
  have hwexpr0 : 0 ≤ d.w0 12766 163 + d.w1 12766 163 * √(π / 2) +
      2 * d.w2 12766 163 + energyR16 12766 *
      radiusPolynomialRoot16 (d.w0 12766 163) (d.w1 12766 163) (d.w2 12766 163) := by
    positivity
  constructor
  · change (12766 : ℝ) ^ 8 * (mA 12766 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12766 163) (d.f1 12766 163) d.f2 + locationR16 12766 *
        radiusPolynomialRoot16 (d.f0 12766 163) (d.f1 12766 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12766 : ℝ) ^ 8 * (mA 12766 : ℝ) ^ 8 *
        ((((282731113 / 62500000000000000) : ℝ) ^ 2 + 2 * ((282731113 / 62500000000000000)) * ((754591037 / 500000000000000000)) * (126 / 100) +
          2 * (((754591037 / 500000000000000000)) ^ 2 + 2 * ((282731113 / 62500000000000000)) * ((362732447 / 1000000000000000000))) +
          6 * ((754591037 / 500000000000000000)) * ((362732447 / 1000000000000000000)) * (126 / 100) + 8 * ((362732447 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12766) *
          (32 * (((282731113 / 62500000000000000) : ℝ) + (754591037 / 500000000000000000) + (362732447 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12766 : ℝ) ^ 16 *
      (d.w0 12766 163 + d.w1 12766 163 * √(π / 2) + 2 * d.w2 12766 163 +
        energyR16 12766 * radiusPolynomialRoot16 (d.w0 12766 163) (d.w1 12766 163)
          (d.w2 12766 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12766 : ℝ) ^ 16 *
        (((451227973 / 25000000000000000000) : ℝ) + ((642080143 / 50000000000000000000)) * (126 / 100) + 2 * ((234599859 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12766) *
          (32 * (((451227973 / 25000000000000000000) : ℝ) + (642080143 / 50000000000000000000) + (234599859 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12766

/-! A coarse bound on the actual paper statistics constant at dimension 12767. -/
namespace BstLean.Part266.Row12767
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12765 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12765 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12765 128 ≤ (13019 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13019 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12767) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12767 : ℕ))
    (by norm_num : (12767 : ℕ) ≤ 16384)
  have ht : paperTail256 12767 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12767 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12767 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12767 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12767 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12767 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12765 128 * √(2 / (12767 : ℝ)) *
      (√(12767 : ℝ) + paperT0 12767 + paperTail256 12767) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12767 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12767 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12767 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12765 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12765 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12767 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12767

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12767
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12767 (61 / 100) 163 (17 / (100 * 12767)) (26 / (10 * 12767)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12767 (61 / 100) 163 (17 / (100 * 12767)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (93816943 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (367419693 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4904515259 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12767 / 12767 * (61 / 100)) ^ 4 * inverseRadius8 (12767 - 1) /
            envelopeGap 12767 (61 / 100) 163 (17 / (100 * 12767)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12767

namespace BstLean.Part266.Row12767
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12767 163 ≤ (113070307 / 25000000000000000)
  f1 : (tableEnvelope C).f1 12767 163 ≤ (188610827 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (181330713 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12767 163 ≤ (1804487843 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12767 163 ≤ (1283858569 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12767 163 ≤ (234544733 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (93816943 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (93816943 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (367419693 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4904515259 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3649051 / 1000000000) : ℝ) ≤ √(17 / (100 * 12767) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12767) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2165836363 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19168194829 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12767) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12767) ≤ (110771017 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12767) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12767 * (163 : ℝ) ^ 2 + 26 / (10 * 12767) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12767) : ℝ)) (tA 12767 * 163 ^ 2 + 26 / (10 * 12767)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3649051 / 1000000000))) * ((93816943 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3649051 / 1000000000)) ^ 3) * ((367419693 / 250000000000000000000000))) + ((4904515259 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3649051 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12767) : ℝ)) d.D d.V d.P (√(tA 12767) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3649051 / 1000000000)) ^ 2 * (((2165836363 / 1000000000000000)) * ((19168194829 / 500000000000000000)))) + ((4904515259 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12767) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3649051 / 1000000000)) * ((93816943 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12767) : ℝ)) (tA 12767 * 163 ^ 2 + 26 / (10 * 12767)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((93816943 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3649051 / 1000000000)) ^ 2) * ((367419693 / 250000000000000000000000)) + ((4904515259 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12767) : ℝ)) (√(26 / (10 * 12767) : ℝ)) d.D d.V d.P (√(tA 12767) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3649051 / 1000000000)) * (((2165836363 / 1000000000000000)) * ((19168194829 / 500000000000000000))) + ((4904515259 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12767) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((93816943 / 20000000000000000000) : ℝ) + ((4904515259 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12767

namespace BstLean.Part266.Row12767
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12767 163 ∧
    0 ≤ (tableEnvelope C).f1 12767 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12767 163 ∧
    0 ≤ (tableEnvelope C).w1 12767 163 ∧ 0 ≤ (tableEnvelope C).w2 12767 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12767 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12767 163 ∧ 0 ≤ d.f1 12767 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12767 163 ∧ 0 ≤ d.w1 12767 163 ∧ 0 ≤ d.w2 12767 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12767 ≤ 2 * (228 / 100 : ℝ) / 12767 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12767 ≤ 2 * (370 / 100 : ℝ) / 12767 := by
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
    (completeRAData (tableEnvelope C) 12767 163).locationBound 12767 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12767 163).energyBound 12767 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12767 163) (d.f1 12767 163) d.f2 ≤
      32 * (((113070307 / 25000000000000000) : ℝ) + (188610827 / 125000000000000000) + (181330713 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12767 163) (d.w1 12767 163)
      (d.w2 12767 163) ≤
      32 * (((1804487843 / 100000000000000000000) : ℝ) + (1283858569 / 100000000000000000000) + (234544733 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12767 163) (d.f1 12767 163) d.f2 ≤
      ((113070307 / 25000000000000000) : ℝ) ^ 2 + 2 * ((113070307 / 25000000000000000)) * ((188610827 / 125000000000000000)) * (126 / 100) +
      2 * (((188610827 / 125000000000000000)) ^ 2 + 2 * ((113070307 / 25000000000000000)) * ((181330713 / 500000000000000000))) +
      6 * ((188610827 / 125000000000000000)) * ((181330713 / 500000000000000000)) * (126 / 100) + 8 * ((181330713 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12767 163) (d.f1 12767 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12767 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12767 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12767 163) (d.f1 12767 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12767 163) (d.w1 12767 163) (d.w2 12767 163)
  have hwexpr0 : 0 ≤ d.w0 12767 163 + d.w1 12767 163 * √(π / 2) +
      2 * d.w2 12767 163 + energyR16 12767 *
      radiusPolynomialRoot16 (d.w0 12767 163) (d.w1 12767 163) (d.w2 12767 163) := by
    positivity
  constructor
  · change (12767 : ℝ) ^ 8 * (mA 12767 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12767 163) (d.f1 12767 163) d.f2 + locationR16 12767 *
        radiusPolynomialRoot16 (d.f0 12767 163) (d.f1 12767 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12767 : ℝ) ^ 8 * (mA 12767 : ℝ) ^ 8 *
        ((((113070307 / 25000000000000000) : ℝ) ^ 2 + 2 * ((113070307 / 25000000000000000)) * ((188610827 / 125000000000000000)) * (126 / 100) +
          2 * (((188610827 / 125000000000000000)) ^ 2 + 2 * ((113070307 / 25000000000000000)) * ((181330713 / 500000000000000000))) +
          6 * ((188610827 / 125000000000000000)) * ((181330713 / 500000000000000000)) * (126 / 100) + 8 * ((181330713 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12767) *
          (32 * (((113070307 / 25000000000000000) : ℝ) + (188610827 / 125000000000000000) + (181330713 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12767 : ℝ) ^ 16 *
      (d.w0 12767 163 + d.w1 12767 163 * √(π / 2) + 2 * d.w2 12767 163 +
        energyR16 12767 * radiusPolynomialRoot16 (d.w0 12767 163) (d.w1 12767 163)
          (d.w2 12767 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12767 : ℝ) ^ 16 *
        (((1804487843 / 100000000000000000000) : ℝ) + ((1283858569 / 100000000000000000000)) * (126 / 100) + 2 * ((234544733 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12767) *
          (32 * (((1804487843 / 100000000000000000000) : ℝ) + (1283858569 / 100000000000000000000) + (234544733 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12767

/-! A coarse bound on the actual paper statistics constant at dimension 12768. -/
namespace BstLean.Part266.Row12768
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12766 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12766 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12766 128 ≤ (13020 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13020 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12768) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12768 : ℕ))
    (by norm_num : (12768 : ℕ) ≤ 16384)
  have ht : paperTail256 12768 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12768 : ℝ) ≤ 113 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12768 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12768 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12768 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12768 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16) := by
    change exactRadius 12766 128 * √(2 / (12768 : ℝ)) *
      (√(12768 : ℝ) + paperT0 12768 + paperTail256 12768) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12768 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12768 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12768 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12766 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12766 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12768 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (113 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12768

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12768
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12768 (61 / 100) 163 (17 / (100 * 12768)) (26 / (10 * 12768)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12768 (61 / 100) 163 (17 / (100 * 12768)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (468974501 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1469218383 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2450706747 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12768 / 12768 * (61 / 100)) ^ 4 * inverseRadius8 (12768 - 1) /
            envelopeGap 12768 (61 / 100) 163 (17 / (100 * 12768)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12768

namespace BstLean.Part266.Row12768
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12768 163 ≤ (282620441 / 62500000000000000)
  f1 : (tableEnvelope C).f1 12768 163 ≤ (754295627 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (181295213 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12768 163 ≤ (90203197 / 5000000000000000000)
  w1 : (tableEnvelope C).w1 12768 163 ≤ (641778477 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12768 163 ≤ (468979249 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (468974501 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (468974501 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1469218383 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2450706747 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((912227 / 250000000) : ℝ) ≤ √(17 / (100 * 12768) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12768) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2165581911 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38330384593 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12768) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12768) ≤ (110762341 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12768) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12768 * (163 : ℝ) ^ 2 + 26 / (10 * 12768) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12768) : ℝ)) (tA 12768 * 163 ^ 2 + 26 / (10 * 12768)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((912227 / 250000000))) * ((468974501 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((912227 / 250000000)) ^ 3) * ((1469218383 / 1000000000000000000000000))) + ((2450706747 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((912227 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12768) : ℝ)) d.D d.V d.P (√(tA 12768) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((912227 / 250000000)) ^ 2 * (((2165581911 / 1000000000000000)) * ((38330384593 / 1000000000000000000)))) + ((2450706747 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12768) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((912227 / 250000000)) * ((468974501 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12768) : ℝ)) (tA 12768 * 163 ^ 2 + 26 / (10 * 12768)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((468974501 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((912227 / 250000000)) ^ 2) * ((1469218383 / 1000000000000000000000000)) + ((2450706747 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12768) : ℝ)) (√(26 / (10 * 12768) : ℝ)) d.D d.V d.P (√(tA 12768) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((912227 / 250000000)) * (((2165581911 / 1000000000000000)) * ((38330384593 / 1000000000000000000))) + ((2450706747 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12768) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((468974501 / 100000000000000000000) : ℝ) + ((2450706747 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12768

namespace BstLean.Part266.Row12768
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12768 163 ∧
    0 ≤ (tableEnvelope C).f1 12768 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12768 163 ∧
    0 ≤ (tableEnvelope C).w1 12768 163 ∧ 0 ≤ (tableEnvelope C).w2 12768 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12768 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12768 163 ∧ 0 ≤ d.f1 12768 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12768 163 ∧ 0 ≤ d.w1 12768 163 ∧ 0 ≤ d.w2 12768 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12768 ≤ 2 * (228 / 100 : ℝ) / 12768 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12768 ≤ 2 * (370 / 100 : ℝ) / 12768 := by
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
    (completeRAData (tableEnvelope C) 12768 163).locationBound 12768 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12768 163).energyBound 12768 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12768 163) (d.f1 12768 163) d.f2 ≤
      32 * (((282620441 / 62500000000000000) : ℝ) + (754295627 / 500000000000000000) + (181295213 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12768 163) (d.w1 12768 163)
      (d.w2 12768 163) ≤
      32 * (((90203197 / 5000000000000000000) : ℝ) + (641778477 / 50000000000000000000) + (468979249 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12768 163) (d.f1 12768 163) d.f2 ≤
      ((282620441 / 62500000000000000) : ℝ) ^ 2 + 2 * ((282620441 / 62500000000000000)) * ((754295627 / 500000000000000000)) * (126 / 100) +
      2 * (((754295627 / 500000000000000000)) ^ 2 + 2 * ((282620441 / 62500000000000000)) * ((181295213 / 500000000000000000))) +
      6 * ((754295627 / 500000000000000000)) * ((181295213 / 500000000000000000)) * (126 / 100) + 8 * ((181295213 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12768 163) (d.f1 12768 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12768 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12768 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12768 163) (d.f1 12768 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12768 163) (d.w1 12768 163) (d.w2 12768 163)
  have hwexpr0 : 0 ≤ d.w0 12768 163 + d.w1 12768 163 * √(π / 2) +
      2 * d.w2 12768 163 + energyR16 12768 *
      radiusPolynomialRoot16 (d.w0 12768 163) (d.w1 12768 163) (d.w2 12768 163) := by
    positivity
  constructor
  · change (12768 : ℝ) ^ 8 * (mA 12768 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12768 163) (d.f1 12768 163) d.f2 + locationR16 12768 *
        radiusPolynomialRoot16 (d.f0 12768 163) (d.f1 12768 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12768 : ℝ) ^ 8 * (mA 12768 : ℝ) ^ 8 *
        ((((282620441 / 62500000000000000) : ℝ) ^ 2 + 2 * ((282620441 / 62500000000000000)) * ((754295627 / 500000000000000000)) * (126 / 100) +
          2 * (((754295627 / 500000000000000000)) ^ 2 + 2 * ((282620441 / 62500000000000000)) * ((181295213 / 500000000000000000))) +
          6 * ((754295627 / 500000000000000000)) * ((181295213 / 500000000000000000)) * (126 / 100) + 8 * ((181295213 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12768) *
          (32 * (((282620441 / 62500000000000000) : ℝ) + (754295627 / 500000000000000000) + (181295213 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12768 : ℝ) ^ 16 *
      (d.w0 12768 163 + d.w1 12768 163 * √(π / 2) + 2 * d.w2 12768 163 +
        energyR16 12768 * radiusPolynomialRoot16 (d.w0 12768 163) (d.w1 12768 163)
          (d.w2 12768 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12768 : ℝ) ^ 16 *
        (((90203197 / 5000000000000000000) : ℝ) + ((641778477 / 50000000000000000000)) * (126 / 100) + 2 * ((468979249 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12768) *
          (32 * (((90203197 / 5000000000000000000) : ℝ) + (641778477 / 50000000000000000000) + (468979249 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12768

/-! A coarse bound on the actual paper statistics constant at dimension 12769. -/
namespace BstLean.Part266.Row12769
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12767 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12767 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12767 128 ≤ (13021 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13021 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12769) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12769 : ℕ))
    (by norm_num : (12769 : ℕ) ≤ 16384)
  have ht : paperTail256 12769 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12769 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12769 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12769 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12769 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12769 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12767 128 * √(2 / (12769 : ℝ)) *
      (√(12769 : ℝ) + paperT0 12769 + paperTail256 12769) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12769 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12769 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12769 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12767 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12767 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12769 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12769

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12769
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12769 (61 / 100) 163 (17 / (100 * 12769)) (26 / (10 * 12769)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12769 (61 / 100) 163 (17 / (100 * 12769)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (468864321 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1468758173 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4898313937 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12769 / 12769 * (61 / 100)) ^ 4 * inverseRadius8 (12769 - 1) /
            envelopeGap 12769 (61 / 100) 163 (17 / (100 * 12769)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12769

namespace BstLean.Part266.Row12769
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12769 163 ≤ (904207711 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12769 163 ≤ (1508295159 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (362519347 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12769 163 ≤ (1803639449 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12769 163 ≤ (641627543 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12769 163 ≤ (234434533 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (468864321 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (468864321 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1468758173 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4898313937 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1824383 / 500000000) : ℝ) ≤ √(17 / (100 * 12769) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12769) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2165327507 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19162190461 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12769) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12769) ≤ (110753667 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12769) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12769 * (163 : ℝ) ^ 2 + 26 / (10 * 12769) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12769) : ℝ)) (tA 12769 * 163 ^ 2 + 26 / (10 * 12769)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1824383 / 500000000))) * ((468864321 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1824383 / 500000000)) ^ 3) * ((1468758173 / 1000000000000000000000000))) + ((4898313937 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1824383 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12769) : ℝ)) d.D d.V d.P (√(tA 12769) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1824383 / 500000000)) ^ 2 * (((2165327507 / 1000000000000000)) * ((19162190461 / 500000000000000000)))) + ((4898313937 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12769) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1824383 / 500000000)) * ((468864321 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12769) : ℝ)) (tA 12769 * 163 ^ 2 + 26 / (10 * 12769)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((468864321 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1824383 / 500000000)) ^ 2) * ((1468758173 / 1000000000000000000000000)) + ((4898313937 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12769) : ℝ)) (√(26 / (10 * 12769) : ℝ)) d.D d.V d.P (√(tA 12769) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1824383 / 500000000)) * (((2165327507 / 1000000000000000)) * ((19162190461 / 500000000000000000))) + ((4898313937 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12769) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((468864321 / 100000000000000000000) : ℝ) + ((4898313937 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12769

namespace BstLean.Part266.Row12769
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12769 163 ∧
    0 ≤ (tableEnvelope C).f1 12769 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12769 163 ∧
    0 ≤ (tableEnvelope C).w1 12769 163 ∧ 0 ≤ (tableEnvelope C).w2 12769 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12769 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12769 163 ∧ 0 ≤ d.f1 12769 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12769 163 ∧ 0 ≤ d.w1 12769 163 ∧ 0 ≤ d.w2 12769 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12769 ≤ 2 * (228 / 100 : ℝ) / 12769 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12769 ≤ 2 * (370 / 100 : ℝ) / 12769 := by
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
    (completeRAData (tableEnvelope C) 12769 163).locationBound 12769 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12769 163).energyBound 12769 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12769 163) (d.f1 12769 163) d.f2 ≤
      32 * (((904207711 / 200000000000000000) : ℝ) + (1508295159 / 1000000000000000000) + (362519347 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12769 163) (d.w1 12769 163)
      (d.w2 12769 163) ≤
      32 * (((1803639449 / 100000000000000000000) : ℝ) + (641627543 / 50000000000000000000) + (234434533 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12769 163) (d.f1 12769 163) d.f2 ≤
      ((904207711 / 200000000000000000) : ℝ) ^ 2 + 2 * ((904207711 / 200000000000000000)) * ((1508295159 / 1000000000000000000)) * (126 / 100) +
      2 * (((1508295159 / 1000000000000000000)) ^ 2 + 2 * ((904207711 / 200000000000000000)) * ((362519347 / 1000000000000000000))) +
      6 * ((1508295159 / 1000000000000000000)) * ((362519347 / 1000000000000000000)) * (126 / 100) + 8 * ((362519347 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12769 163) (d.f1 12769 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12769 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12769 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12769 163) (d.f1 12769 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12769 163) (d.w1 12769 163) (d.w2 12769 163)
  have hwexpr0 : 0 ≤ d.w0 12769 163 + d.w1 12769 163 * √(π / 2) +
      2 * d.w2 12769 163 + energyR16 12769 *
      radiusPolynomialRoot16 (d.w0 12769 163) (d.w1 12769 163) (d.w2 12769 163) := by
    positivity
  constructor
  · change (12769 : ℝ) ^ 8 * (mA 12769 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12769 163) (d.f1 12769 163) d.f2 + locationR16 12769 *
        radiusPolynomialRoot16 (d.f0 12769 163) (d.f1 12769 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12769 : ℝ) ^ 8 * (mA 12769 : ℝ) ^ 8 *
        ((((904207711 / 200000000000000000) : ℝ) ^ 2 + 2 * ((904207711 / 200000000000000000)) * ((1508295159 / 1000000000000000000)) * (126 / 100) +
          2 * (((1508295159 / 1000000000000000000)) ^ 2 + 2 * ((904207711 / 200000000000000000)) * ((362519347 / 1000000000000000000))) +
          6 * ((1508295159 / 1000000000000000000)) * ((362519347 / 1000000000000000000)) * (126 / 100) + 8 * ((362519347 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12769) *
          (32 * (((904207711 / 200000000000000000) : ℝ) + (1508295159 / 1000000000000000000) + (362519347 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12769 : ℝ) ^ 16 *
      (d.w0 12769 163 + d.w1 12769 163 * √(π / 2) + 2 * d.w2 12769 163 +
        energyR16 12769 * radiusPolynomialRoot16 (d.w0 12769 163) (d.w1 12769 163)
          (d.w2 12769 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12769 : ℝ) ^ 16 *
        (((1803639449 / 100000000000000000000) : ℝ) + ((641627543 / 50000000000000000000)) * (126 / 100) + 2 * ((234434533 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12769) *
          (32 * (((1803639449 / 100000000000000000000) : ℝ) + (641627543 / 50000000000000000000) + (234434533 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12769

/-! A coarse bound on the actual paper statistics constant at dimension 12770. -/
namespace BstLean.Part266.Row12770
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12768 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12768 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12768 128 ≤ (13022 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13022 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12770) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12770 : ℕ))
    (by norm_num : (12770 : ℕ) ≤ 16384)
  have ht : paperTail256 12770 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12770 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12770 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12770 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12770 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12770 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12768 128 * √(2 / (12770 : ℝ)) *
      (√(12770 : ℝ) + paperT0 12770 + paperTail256 12770) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12770 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12770 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12770 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12768 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12768 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12770 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12770

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12770
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12770 (61 / 100) 163 (17 / (100 * 12770)) (26 / (10 * 12770)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12770 (61 / 100) 163 (17 / (100 * 12770)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (1831071 / 390625000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (45884317 / 31250000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1223804147 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12770 / 12770 * (61 / 100)) ^ 4 * inverseRadius8 (12770 - 1) /
            envelopeGap 12770 (61 / 100) 163 (17 / (100 * 12770)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12770

namespace BstLean.Part266.Row12770
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12770 163 ≤ (282509621 / 62500000000000000)
  f1 : (tableEnvelope C).f1 12770 163 ≤ (1507999987 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (362448389 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12770 163 ≤ (450803959 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12770 163 ≤ (160369209 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 12770 163 ≤ (234379459 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (1831071 / 390625000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (1831071 / 390625000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (45884317 / 31250000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1223804147 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3648623 / 1000000000) : ℝ) ≤ √(17 / (100 * 12770) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12770) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1082536577 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (2394898667 / 62500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12770) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12770) ≤ (55372497 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12770) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12770 * (163 : ℝ) ^ 2 + 26 / (10 * 12770) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12770) : ℝ)) (tA 12770 * 163 ^ 2 + 26 / (10 * 12770)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3648623 / 1000000000))) * ((1831071 / 390625000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3648623 / 1000000000)) ^ 3) * ((45884317 / 31250000000000000000000))) + ((1223804147 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3648623 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12770) : ℝ)) d.D d.V d.P (√(tA 12770) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3648623 / 1000000000)) ^ 2 * (((1082536577 / 500000000000000)) * ((2394898667 / 62500000000000000)))) + ((1223804147 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12770) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3648623 / 1000000000)) * ((1831071 / 390625000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12770) : ℝ)) (tA 12770 * 163 ^ 2 + 26 / (10 * 12770)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((1831071 / 390625000000000000) : ℝ) + (24198 / 100000) / (2 * ((3648623 / 1000000000)) ^ 2) * ((45884317 / 31250000000000000000000)) + ((1223804147 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12770) : ℝ)) (√(26 / (10 * 12770) : ℝ)) d.D d.V d.P (√(tA 12770) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3648623 / 1000000000)) * (((1082536577 / 500000000000000)) * ((2394898667 / 62500000000000000))) + ((1223804147 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12770) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((1831071 / 390625000000000000) : ℝ) + ((1223804147 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12770

namespace BstLean.Part266.Row12770
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12770 163 ∧
    0 ≤ (tableEnvelope C).f1 12770 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12770 163 ∧
    0 ≤ (tableEnvelope C).w1 12770 163 ∧ 0 ≤ (tableEnvelope C).w2 12770 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12770 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12770 163 ∧ 0 ≤ d.f1 12770 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12770 163 ∧ 0 ≤ d.w1 12770 163 ∧ 0 ≤ d.w2 12770 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12770 ≤ 2 * (228 / 100 : ℝ) / 12770 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12770 ≤ 2 * (370 / 100 : ℝ) / 12770 := by
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
    (completeRAData (tableEnvelope C) 12770 163).locationBound 12770 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12770 163).energyBound 12770 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12770 163) (d.f1 12770 163) d.f2 ≤
      32 * (((282509621 / 62500000000000000) : ℝ) + (1507999987 / 1000000000000000000) + (362448389 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12770 163) (d.w1 12770 163)
      (d.w2 12770 163) ≤
      32 * (((450803959 / 25000000000000000000) : ℝ) + (160369209 / 12500000000000000000) + (234379459 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12770 163) (d.f1 12770 163) d.f2 ≤
      ((282509621 / 62500000000000000) : ℝ) ^ 2 + 2 * ((282509621 / 62500000000000000)) * ((1507999987 / 1000000000000000000)) * (126 / 100) +
      2 * (((1507999987 / 1000000000000000000)) ^ 2 + 2 * ((282509621 / 62500000000000000)) * ((362448389 / 1000000000000000000))) +
      6 * ((1507999987 / 1000000000000000000)) * ((362448389 / 1000000000000000000)) * (126 / 100) + 8 * ((362448389 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12770 163) (d.f1 12770 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12770 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12770 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12770 163) (d.f1 12770 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12770 163) (d.w1 12770 163) (d.w2 12770 163)
  have hwexpr0 : 0 ≤ d.w0 12770 163 + d.w1 12770 163 * √(π / 2) +
      2 * d.w2 12770 163 + energyR16 12770 *
      radiusPolynomialRoot16 (d.w0 12770 163) (d.w1 12770 163) (d.w2 12770 163) := by
    positivity
  constructor
  · change (12770 : ℝ) ^ 8 * (mA 12770 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12770 163) (d.f1 12770 163) d.f2 + locationR16 12770 *
        radiusPolynomialRoot16 (d.f0 12770 163) (d.f1 12770 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12770 : ℝ) ^ 8 * (mA 12770 : ℝ) ^ 8 *
        ((((282509621 / 62500000000000000) : ℝ) ^ 2 + 2 * ((282509621 / 62500000000000000)) * ((1507999987 / 1000000000000000000)) * (126 / 100) +
          2 * (((1507999987 / 1000000000000000000)) ^ 2 + 2 * ((282509621 / 62500000000000000)) * ((362448389 / 1000000000000000000))) +
          6 * ((1507999987 / 1000000000000000000)) * ((362448389 / 1000000000000000000)) * (126 / 100) + 8 * ((362448389 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12770) *
          (32 * (((282509621 / 62500000000000000) : ℝ) + (1507999987 / 1000000000000000000) + (362448389 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12770 : ℝ) ^ 16 *
      (d.w0 12770 163 + d.w1 12770 163 * √(π / 2) + 2 * d.w2 12770 163 +
        energyR16 12770 * radiusPolynomialRoot16 (d.w0 12770 163) (d.w1 12770 163)
          (d.w2 12770 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12770 : ℝ) ^ 16 *
        (((450803959 / 25000000000000000000) : ℝ) + ((160369209 / 12500000000000000000)) * (126 / 100) + 2 * ((234379459 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12770) *
          (32 * (((450803959 / 25000000000000000000) : ℝ) + (160369209 / 12500000000000000000) + (234379459 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12770

/-! A coarse bound on the actual paper statistics constant at dimension 12771. -/
namespace BstLean.Part266.Row12771
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12769 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12769 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12769 128 ≤ (13023 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13023 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12771) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12771 : ℕ))
    (by norm_num : (12771 : ℕ) ≤ 16384)
  have ht : paperTail256 12771 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12771 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12771 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12771 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12771 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12771 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12769 128 * √(2 / (12771 : ℝ)) *
      (√(12771 : ℝ) + paperT0 12771 + paperTail256 12771) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12771 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12771 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12771 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12769 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12769 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12771 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12771

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12771
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12771 (61 / 100) 163 (17 / (100 * 12771)) (26 / (10 * 12771)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12771 (61 / 100) 163 (17 / (100 * 12771)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (93728813 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (293567659 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (978424289 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12771 / 12771 * (61 / 100)) ^ 4 * inverseRadius8 (12771 - 1) /
            envelopeGap 12771 (61 / 100) 163 (17 / (100 * 12771)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12771

namespace BstLean.Part266.Row12771
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12771 163 ≤ (2259634809 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12771 163 ≤ (1507704909 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (90594363 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12771 163 ≤ (1802792367 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12771 163 ≤ (320663089 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12771 163 ≤ (117162201 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (93728813 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (93728813 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (293567659 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (978424289 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((22803 / 6250000) : ℝ) ≤ √(17 / (100 * 12771) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12771) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (43296377 / 20000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38312377831 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12771) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12771) ≤ (55368161 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12771) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12771 * (163 : ℝ) ^ 2 + 26 / (10 * 12771) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12771) : ℝ)) (tA 12771 * 163 ^ 2 + 26 / (10 * 12771)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((22803 / 6250000))) * ((93728813 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((22803 / 6250000)) ^ 3) * ((293567659 / 200000000000000000000000))) + ((978424289 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((22803 / 6250000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12771) : ℝ)) d.D d.V d.P (√(tA 12771) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((22803 / 6250000)) ^ 2 * (((43296377 / 20000000000000)) * ((38312377831 / 1000000000000000000)))) + ((978424289 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12771) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((22803 / 6250000)) * ((93728813 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12771) : ℝ)) (tA 12771 * 163 ^ 2 + 26 / (10 * 12771)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((93728813 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((22803 / 6250000)) ^ 2) * ((293567659 / 200000000000000000000000)) + ((978424289 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12771) : ℝ)) (√(26 / (10 * 12771) : ℝ)) d.D d.V d.P (√(tA 12771) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((22803 / 6250000)) * (((43296377 / 20000000000000)) * ((38312377831 / 1000000000000000000))) + ((978424289 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12771) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((93728813 / 20000000000000000000) : ℝ) + ((978424289 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12771

namespace BstLean.Part266.Row12771
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12771 163 ∧
    0 ≤ (tableEnvelope C).f1 12771 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12771 163 ∧
    0 ≤ (tableEnvelope C).w1 12771 163 ∧ 0 ≤ (tableEnvelope C).w2 12771 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12771 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12771 163 ∧ 0 ≤ d.f1 12771 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12771 163 ∧ 0 ≤ d.w1 12771 163 ∧ 0 ≤ d.w2 12771 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12771 ≤ 2 * (228 / 100 : ℝ) / 12771 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12771 ≤ 2 * (370 / 100 : ℝ) / 12771 := by
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
    (completeRAData (tableEnvelope C) 12771 163).locationBound 12771 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12771 163).energyBound 12771 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12771 163) (d.f1 12771 163) d.f2 ≤
      32 * (((2259634809 / 500000000000000000) : ℝ) + (1507704909 / 1000000000000000000) + (90594363 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12771 163) (d.w1 12771 163)
      (d.w2 12771 163) ≤
      32 * (((1802792367 / 100000000000000000000) : ℝ) + (320663089 / 25000000000000000000) + (117162201 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12771 163) (d.f1 12771 163) d.f2 ≤
      ((2259634809 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2259634809 / 500000000000000000)) * ((1507704909 / 1000000000000000000)) * (126 / 100) +
      2 * (((1507704909 / 1000000000000000000)) ^ 2 + 2 * ((2259634809 / 500000000000000000)) * ((90594363 / 250000000000000000))) +
      6 * ((1507704909 / 1000000000000000000)) * ((90594363 / 250000000000000000)) * (126 / 100) + 8 * ((90594363 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12771 163) (d.f1 12771 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12771 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12771 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12771 163) (d.f1 12771 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12771 163) (d.w1 12771 163) (d.w2 12771 163)
  have hwexpr0 : 0 ≤ d.w0 12771 163 + d.w1 12771 163 * √(π / 2) +
      2 * d.w2 12771 163 + energyR16 12771 *
      radiusPolynomialRoot16 (d.w0 12771 163) (d.w1 12771 163) (d.w2 12771 163) := by
    positivity
  constructor
  · change (12771 : ℝ) ^ 8 * (mA 12771 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12771 163) (d.f1 12771 163) d.f2 + locationR16 12771 *
        radiusPolynomialRoot16 (d.f0 12771 163) (d.f1 12771 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12771 : ℝ) ^ 8 * (mA 12771 : ℝ) ^ 8 *
        ((((2259634809 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2259634809 / 500000000000000000)) * ((1507704909 / 1000000000000000000)) * (126 / 100) +
          2 * (((1507704909 / 1000000000000000000)) ^ 2 + 2 * ((2259634809 / 500000000000000000)) * ((90594363 / 250000000000000000))) +
          6 * ((1507704909 / 1000000000000000000)) * ((90594363 / 250000000000000000)) * (126 / 100) + 8 * ((90594363 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12771) *
          (32 * (((2259634809 / 500000000000000000) : ℝ) + (1507704909 / 1000000000000000000) + (90594363 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12771 : ℝ) ^ 16 *
      (d.w0 12771 163 + d.w1 12771 163 * √(π / 2) + 2 * d.w2 12771 163 +
        energyR16 12771 * radiusPolynomialRoot16 (d.w0 12771 163) (d.w1 12771 163)
          (d.w2 12771 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12771 : ℝ) ^ 16 *
        (((1802792367 / 100000000000000000000) : ℝ) + ((320663089 / 25000000000000000000)) * (126 / 100) + 2 * ((117162201 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12771) *
          (32 * (((1802792367 / 100000000000000000000) : ℝ) + (320663089 / 25000000000000000000) + (117162201 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12771

/-! A coarse bound on the actual paper statistics constant at dimension 12772. -/
namespace BstLean.Part266.Row12772
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12770 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12770 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12770 128 ≤ (13024 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13024 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12772) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12772 : ℕ))
    (by norm_num : (12772 : ℕ) ≤ 16384)
  have ht : paperTail256 12772 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12772 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12772 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12772 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12772 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12772 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12770 128 * √(2 / (12772 : ℝ)) *
      (√(12772 : ℝ) + paperT0 12772 + paperTail256 12772) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12772 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12772 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12772 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12770 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12770 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12772 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12772

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12772
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12772 (61 / 100) 163 (17 / (100 * 12772)) (26 / (10 * 12772)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12772 (61 / 100) 163 (17 / (100 * 12772)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (468533989 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (733689313 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (977805701 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12772 / 12772 * (61 / 100)) ^ 4 * inverseRadius8 (12772 - 1) /
            envelopeGap 12772 (61 / 100) 163 (17 / (100 * 12772)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12772

namespace BstLean.Part266.Row12772
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12772 163 ≤ (1129596401 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12772 163 ≤ (753704963 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (362306537 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12772 163 ≤ (450592261 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12772 163 ≤ (641175571 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12772 163 ≤ (18741549 / 4000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (468533989 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (468533989 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (733689313 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (977805701 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3648337 / 1000000000) : ℝ) ≤ √(17 / (100 * 12772) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12772) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (541141149 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38306378399 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12772) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12772) ≤ (27681913 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12772) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12772 * (163 : ℝ) ^ 2 + 26 / (10 * 12772) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12772) : ℝ)) (tA 12772 * 163 ^ 2 + 26 / (10 * 12772)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3648337 / 1000000000))) * ((468533989 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3648337 / 1000000000)) ^ 3) * ((733689313 / 500000000000000000000000))) + ((977805701 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3648337 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12772) : ℝ)) d.D d.V d.P (√(tA 12772) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3648337 / 1000000000)) ^ 2 * (((541141149 / 250000000000000)) * ((38306378399 / 1000000000000000000)))) + ((977805701 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12772) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3648337 / 1000000000)) * ((468533989 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12772) : ℝ)) (tA 12772 * 163 ^ 2 + 26 / (10 * 12772)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((468533989 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3648337 / 1000000000)) ^ 2) * ((733689313 / 500000000000000000000000)) + ((977805701 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12772) : ℝ)) (√(26 / (10 * 12772) : ℝ)) d.D d.V d.P (√(tA 12772) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3648337 / 1000000000)) * (((541141149 / 250000000000000)) * ((38306378399 / 1000000000000000000))) + ((977805701 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12772) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((468533989 / 100000000000000000000) : ℝ) + ((977805701 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12772

namespace BstLean.Part266.Row12772
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12772 163 ∧
    0 ≤ (tableEnvelope C).f1 12772 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12772 163 ∧
    0 ≤ (tableEnvelope C).w1 12772 163 ∧ 0 ≤ (tableEnvelope C).w2 12772 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12772 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12772 163 ∧ 0 ≤ d.f1 12772 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12772 163 ∧ 0 ≤ d.w1 12772 163 ∧ 0 ≤ d.w2 12772 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12772 ≤ 2 * (228 / 100 : ℝ) / 12772 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12772 ≤ 2 * (370 / 100 : ℝ) / 12772 := by
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
    (completeRAData (tableEnvelope C) 12772 163).locationBound 12772 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12772 163).energyBound 12772 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12772 163) (d.f1 12772 163) d.f2 ≤
      32 * (((1129596401 / 250000000000000000) : ℝ) + (753704963 / 500000000000000000) + (362306537 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12772 163) (d.w1 12772 163)
      (d.w2 12772 163) ≤
      32 * (((450592261 / 25000000000000000000) : ℝ) + (641175571 / 50000000000000000000) + (18741549 / 4000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12772 163) (d.f1 12772 163) d.f2 ≤
      ((1129596401 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1129596401 / 250000000000000000)) * ((753704963 / 500000000000000000)) * (126 / 100) +
      2 * (((753704963 / 500000000000000000)) ^ 2 + 2 * ((1129596401 / 250000000000000000)) * ((362306537 / 1000000000000000000))) +
      6 * ((753704963 / 500000000000000000)) * ((362306537 / 1000000000000000000)) * (126 / 100) + 8 * ((362306537 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12772 163) (d.f1 12772 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12772 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12772 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12772 163) (d.f1 12772 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12772 163) (d.w1 12772 163) (d.w2 12772 163)
  have hwexpr0 : 0 ≤ d.w0 12772 163 + d.w1 12772 163 * √(π / 2) +
      2 * d.w2 12772 163 + energyR16 12772 *
      radiusPolynomialRoot16 (d.w0 12772 163) (d.w1 12772 163) (d.w2 12772 163) := by
    positivity
  constructor
  · change (12772 : ℝ) ^ 8 * (mA 12772 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12772 163) (d.f1 12772 163) d.f2 + locationR16 12772 *
        radiusPolynomialRoot16 (d.f0 12772 163) (d.f1 12772 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12772 : ℝ) ^ 8 * (mA 12772 : ℝ) ^ 8 *
        ((((1129596401 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1129596401 / 250000000000000000)) * ((753704963 / 500000000000000000)) * (126 / 100) +
          2 * (((753704963 / 500000000000000000)) ^ 2 + 2 * ((1129596401 / 250000000000000000)) * ((362306537 / 1000000000000000000))) +
          6 * ((753704963 / 500000000000000000)) * ((362306537 / 1000000000000000000)) * (126 / 100) + 8 * ((362306537 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12772) *
          (32 * (((1129596401 / 250000000000000000) : ℝ) + (753704963 / 500000000000000000) + (362306537 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12772 : ℝ) ^ 16 *
      (d.w0 12772 163 + d.w1 12772 163 * √(π / 2) + 2 * d.w2 12772 163 +
        energyR16 12772 * radiusPolynomialRoot16 (d.w0 12772 163) (d.w1 12772 163)
          (d.w2 12772 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12772 : ℝ) ^ 16 *
        (((450592261 / 25000000000000000000) : ℝ) + ((641175571 / 50000000000000000000)) * (126 / 100) + 2 * ((18741549 / 4000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12772) *
          (32 * (((450592261 / 25000000000000000000) : ℝ) + (641175571 / 50000000000000000000) + (18741549 / 4000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12772

/-! A coarse bound on the actual paper statistics constant at dimension 12773. -/
namespace BstLean.Part266.Row12773
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12771 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12771 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12771 128 ≤ (13025 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13025 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12773) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12773 : ℕ))
    (by norm_num : (12773 : ℕ) ≤ 16384)
  have ht : paperTail256 12773 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12773 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12773 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12773 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12773 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12773 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12771 128 * √(2 / (12773 : ℝ)) *
      (√(12773 : ℝ) + paperT0 12773 + paperTail256 12773) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12773 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12773 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12773 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12771 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12771 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12773 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12773

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12773
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12773 (61 / 100) 163 (17 / (100 * 12773)) (26 / (10 * 12773)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12773 (61 / 100) 163 (17 / (100 * 12773)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (468423947 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1466919137 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4885937767 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12773 / 12773 * (61 / 100)) ^ 4 * inverseRadius8 (12773 - 1) /
            envelopeGap 12773 (61 / 100) 163 (17 / (100 * 12773)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12773

namespace BstLean.Part266.Row12773
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12773 163 ≤ (4517501891 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12773 163 ≤ (1507115037 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (181117821 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12773 163 ≤ (360389173 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12773 163 ≤ (320512507 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12773 163 ≤ (11710717 / 2500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (468423947 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (468423947 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1466919137 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4885937767 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1824097 / 500000000) : ℝ) ≤ √(17 / (100 * 12773) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12773) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (270538799 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38300380377 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12773) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12773) ≤ (110718983 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12773) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12773 * (163 : ℝ) ^ 2 + 26 / (10 * 12773) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12773) : ℝ)) (tA 12773 * 163 ^ 2 + 26 / (10 * 12773)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1824097 / 500000000))) * ((468423947 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1824097 / 500000000)) ^ 3) * ((1466919137 / 1000000000000000000000000))) + ((4885937767 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1824097 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12773) : ℝ)) d.D d.V d.P (√(tA 12773) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1824097 / 500000000)) ^ 2 * (((270538799 / 125000000000000)) * ((38300380377 / 1000000000000000000)))) + ((4885937767 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12773) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1824097 / 500000000)) * ((468423947 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12773) : ℝ)) (tA 12773 * 163 ^ 2 + 26 / (10 * 12773)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((468423947 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1824097 / 500000000)) ^ 2) * ((1466919137 / 1000000000000000000000000)) + ((4885937767 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12773) : ℝ)) (√(26 / (10 * 12773) : ℝ)) d.D d.V d.P (√(tA 12773) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1824097 / 500000000)) * (((270538799 / 125000000000000)) * ((38300380377 / 1000000000000000000))) + ((4885937767 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12773) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((468423947 / 100000000000000000000) : ℝ) + ((4885937767 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12773

namespace BstLean.Part266.Row12773
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12773 163 ∧
    0 ≤ (tableEnvelope C).f1 12773 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12773 163 ∧
    0 ≤ (tableEnvelope C).w1 12773 163 ∧ 0 ≤ (tableEnvelope C).w2 12773 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12773 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12773 163 ∧ 0 ≤ d.f1 12773 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12773 163 ∧ 0 ≤ d.w1 12773 163 ∧ 0 ≤ d.w2 12773 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12773 ≤ 2 * (228 / 100 : ℝ) / 12773 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12773 ≤ 2 * (370 / 100 : ℝ) / 12773 := by
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
    (completeRAData (tableEnvelope C) 12773 163).locationBound 12773 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12773 163).energyBound 12773 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12773 163) (d.f1 12773 163) d.f2 ≤
      32 * (((4517501891 / 1000000000000000000) : ℝ) + (1507115037 / 1000000000000000000) + (181117821 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12773 163) (d.w1 12773 163)
      (d.w2 12773 163) ≤
      32 * (((360389173 / 20000000000000000000) : ℝ) + (320512507 / 25000000000000000000) + (11710717 / 2500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12773 163) (d.f1 12773 163) d.f2 ≤
      ((4517501891 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4517501891 / 1000000000000000000)) * ((1507115037 / 1000000000000000000)) * (126 / 100) +
      2 * (((1507115037 / 1000000000000000000)) ^ 2 + 2 * ((4517501891 / 1000000000000000000)) * ((181117821 / 500000000000000000))) +
      6 * ((1507115037 / 1000000000000000000)) * ((181117821 / 500000000000000000)) * (126 / 100) + 8 * ((181117821 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12773 163) (d.f1 12773 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12773 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12773 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12773 163) (d.f1 12773 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12773 163) (d.w1 12773 163) (d.w2 12773 163)
  have hwexpr0 : 0 ≤ d.w0 12773 163 + d.w1 12773 163 * √(π / 2) +
      2 * d.w2 12773 163 + energyR16 12773 *
      radiusPolynomialRoot16 (d.w0 12773 163) (d.w1 12773 163) (d.w2 12773 163) := by
    positivity
  constructor
  · change (12773 : ℝ) ^ 8 * (mA 12773 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12773 163) (d.f1 12773 163) d.f2 + locationR16 12773 *
        radiusPolynomialRoot16 (d.f0 12773 163) (d.f1 12773 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12773 : ℝ) ^ 8 * (mA 12773 : ℝ) ^ 8 *
        ((((4517501891 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4517501891 / 1000000000000000000)) * ((1507115037 / 1000000000000000000)) * (126 / 100) +
          2 * (((1507115037 / 1000000000000000000)) ^ 2 + 2 * ((4517501891 / 1000000000000000000)) * ((181117821 / 500000000000000000))) +
          6 * ((1507115037 / 1000000000000000000)) * ((181117821 / 500000000000000000)) * (126 / 100) + 8 * ((181117821 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12773) *
          (32 * (((4517501891 / 1000000000000000000) : ℝ) + (1507115037 / 1000000000000000000) + (181117821 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12773 : ℝ) ^ 16 *
      (d.w0 12773 163 + d.w1 12773 163 * √(π / 2) + 2 * d.w2 12773 163 +
        energyR16 12773 * radiusPolynomialRoot16 (d.w0 12773 163) (d.w1 12773 163)
          (d.w2 12773 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12773 : ℝ) ^ 16 *
        (((360389173 / 20000000000000000000) : ℝ) + ((320512507 / 25000000000000000000)) * (126 / 100) + 2 * ((11710717 / 2500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12773) *
          (32 * (((360389173 / 20000000000000000000) : ℝ) + (320512507 / 25000000000000000000) + (11710717 / 2500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12773

/-! A coarse bound on the actual paper statistics constant at dimension 12774. -/
namespace BstLean.Part266.Row12774
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12772 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12772 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12772 128 ≤ (13026 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13026 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12774) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12774 : ℕ))
    (by norm_num : (12774 : ℕ) ≤ 16384)
  have ht : paperTail256 12774 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12774 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12774 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12774 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12774 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12774 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12772 128 * √(2 / (12774 : ℝ)) *
      (√(12774 : ℝ) + paperT0 12774 + paperTail256 12774) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12774 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12774 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12774 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12772 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12772 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12774 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12774

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12774
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12774 (61 / 100) 163 (17 / (100 * 12774)) (26 / (10 * 12774)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12774 (61 / 100) 163 (17 / (100 * 12774)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (468313939 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1466459827 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4882849229 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12774 / 12774 * (61 / 100)) ^ 4 * inverseRadius8 (12774 - 1) /
            envelopeGap 12774 (61 / 100) 163 (17 / (100 * 12774)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12774

namespace BstLean.Part266.Row12774
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12774 163 ≤ (2258309239 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12774 163 ≤ (753410121 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (11317649 / 31250000000000000)
  w0 : (tableEnvelope C).w0 12774 163 ≤ (1801522829 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12774 163 ≤ (320437253 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12774 163 ≤ (468318669 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (468313939 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (468313939 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1466459827 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4882849229 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3648051 / 1000000000) : ℝ) ≤ √(17 / (100 * 12774) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12774) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (541014059 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38294383753 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12774) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12774) ≤ (22142063 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12774) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12774 * (163 : ℝ) ^ 2 + 26 / (10 * 12774) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12774) : ℝ)) (tA 12774 * 163 ^ 2 + 26 / (10 * 12774)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3648051 / 1000000000))) * ((468313939 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3648051 / 1000000000)) ^ 3) * ((1466459827 / 1000000000000000000000000))) + ((4882849229 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3648051 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12774) : ℝ)) d.D d.V d.P (√(tA 12774) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3648051 / 1000000000)) ^ 2 * (((541014059 / 250000000000000)) * ((38294383753 / 1000000000000000000)))) + ((4882849229 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12774) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3648051 / 1000000000)) * ((468313939 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12774) : ℝ)) (tA 12774 * 163 ^ 2 + 26 / (10 * 12774)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((468313939 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3648051 / 1000000000)) ^ 2) * ((1466459827 / 1000000000000000000000000)) + ((4882849229 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12774) : ℝ)) (√(26 / (10 * 12774) : ℝ)) d.D d.V d.P (√(tA 12774) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3648051 / 1000000000)) * (((541014059 / 250000000000000)) * ((38294383753 / 1000000000000000000))) + ((4882849229 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12774) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((468313939 / 100000000000000000000) : ℝ) + ((4882849229 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12774

namespace BstLean.Part266.Row12774
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12774 163 ∧
    0 ≤ (tableEnvelope C).f1 12774 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12774 163 ∧
    0 ≤ (tableEnvelope C).w1 12774 163 ∧ 0 ≤ (tableEnvelope C).w2 12774 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12774 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12774 163 ∧ 0 ≤ d.f1 12774 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12774 163 ∧ 0 ≤ d.w1 12774 163 ∧ 0 ≤ d.w2 12774 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12774 ≤ 2 * (228 / 100 : ℝ) / 12774 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12774 ≤ 2 * (370 / 100 : ℝ) / 12774 := by
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
    (completeRAData (tableEnvelope C) 12774 163).locationBound 12774 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12774 163).energyBound 12774 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12774 163) (d.f1 12774 163) d.f2 ≤
      32 * (((2258309239 / 500000000000000000) : ℝ) + (753410121 / 500000000000000000) + (11317649 / 31250000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12774 163) (d.w1 12774 163)
      (d.w2 12774 163) ≤
      32 * (((1801522829 / 100000000000000000000) : ℝ) + (320437253 / 25000000000000000000) + (468318669 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12774 163) (d.f1 12774 163) d.f2 ≤
      ((2258309239 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2258309239 / 500000000000000000)) * ((753410121 / 500000000000000000)) * (126 / 100) +
      2 * (((753410121 / 500000000000000000)) ^ 2 + 2 * ((2258309239 / 500000000000000000)) * ((11317649 / 31250000000000000))) +
      6 * ((753410121 / 500000000000000000)) * ((11317649 / 31250000000000000)) * (126 / 100) + 8 * ((11317649 / 31250000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12774 163) (d.f1 12774 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12774 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12774 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12774 163) (d.f1 12774 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12774 163) (d.w1 12774 163) (d.w2 12774 163)
  have hwexpr0 : 0 ≤ d.w0 12774 163 + d.w1 12774 163 * √(π / 2) +
      2 * d.w2 12774 163 + energyR16 12774 *
      radiusPolynomialRoot16 (d.w0 12774 163) (d.w1 12774 163) (d.w2 12774 163) := by
    positivity
  constructor
  · change (12774 : ℝ) ^ 8 * (mA 12774 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12774 163) (d.f1 12774 163) d.f2 + locationR16 12774 *
        radiusPolynomialRoot16 (d.f0 12774 163) (d.f1 12774 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12774 : ℝ) ^ 8 * (mA 12774 : ℝ) ^ 8 *
        ((((2258309239 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2258309239 / 500000000000000000)) * ((753410121 / 500000000000000000)) * (126 / 100) +
          2 * (((753410121 / 500000000000000000)) ^ 2 + 2 * ((2258309239 / 500000000000000000)) * ((11317649 / 31250000000000000))) +
          6 * ((753410121 / 500000000000000000)) * ((11317649 / 31250000000000000)) * (126 / 100) + 8 * ((11317649 / 31250000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12774) *
          (32 * (((2258309239 / 500000000000000000) : ℝ) + (753410121 / 500000000000000000) + (11317649 / 31250000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12774 : ℝ) ^ 16 *
      (d.w0 12774 163 + d.w1 12774 163 * √(π / 2) + 2 * d.w2 12774 163 +
        energyR16 12774 * radiusPolynomialRoot16 (d.w0 12774 163) (d.w1 12774 163)
          (d.w2 12774 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12774 : ℝ) ^ 16 *
        (((1801522829 / 100000000000000000000) : ℝ) + ((320437253 / 25000000000000000000)) * (126 / 100) + 2 * ((468318669 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12774) *
          (32 * (((1801522829 / 100000000000000000000) : ℝ) + (320437253 / 25000000000000000000) + (468318669 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12774
