import BstLean.Part266Shard27Step4


/-! A coarse bound on the actual paper statistics constant at dimension 13025. -/
namespace BstLean.Part266.Row13025
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13023 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13023 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13023 128 ≤ (13277 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13277 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13025) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13025 : ℕ))
    (by norm_num : (13025 : ℕ) ≤ 16384)
  have ht : paperTail256 13025 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13025 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13025 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13025 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13025 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13025 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13023 128 * √(2 / (13025 : ℝ)) *
      (√(13025 : ℝ) + paperT0 13025 + paperTail256 13025) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13025 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13025 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13025 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13023 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13023 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13025 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13025

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13025
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13025 (61 / 100) 165 (17 / (100 * 13025)) (26 / (10 * 13025)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13025 (61 / 100) 165 (17 / (100 * 13025)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (55219609 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (678321501 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (835306071 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13025 / 13025 * (61 / 100)) ^ 4 * inverseRadius8 (13025 - 1) /
            envelopeGap 13025 (61 / 100) 165 (17 / (100 * 13025)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13025

namespace BstLean.Part266.Row13025
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13025 165 ≤ (4302144571 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13025 165 ≤ (1435268129 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (21560451 / 62500000000000000)
  w0 : (tableEnvelope C).w0 13025 165 ≤ (849681099 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13025 165 ≤ (12090637 / 1000000000000000000)
  w2 : (tableEnvelope C).w2 13025 165 ≤ (220880459 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (55219609 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (55219609 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (678321501 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (835306071 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((361273 / 100000000) : ℝ) ≤ √(17 / (100 * 13025) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13025) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (262725163 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36832635013 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13025) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13025) ≤ (108576857 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13025) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13025 * (165 : ℝ) ^ 2 + 26 / (10 * 13025) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13025) : ℝ)) (tA 13025 * 165 ^ 2 + 26 / (10 * 13025)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((361273 / 100000000))) * ((55219609 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((361273 / 100000000)) ^ 3) * ((678321501 / 500000000000000000000000))) + ((835306071 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((361273 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13025) : ℝ)) d.D d.V d.P (√(tA 13025) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((361273 / 100000000)) ^ 2 * (((262725163 / 125000000000000)) * ((36832635013 / 1000000000000000000)))) + ((835306071 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13025) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((361273 / 100000000)) * ((55219609 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13025) : ℝ)) (tA 13025 * 165 ^ 2 + 26 / (10 * 13025)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((55219609 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((361273 / 100000000)) ^ 2) * ((678321501 / 500000000000000000000000)) + ((835306071 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13025) : ℝ)) (√(26 / (10 * 13025) : ℝ)) d.D d.V d.P (√(tA 13025) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((361273 / 100000000)) * (((262725163 / 125000000000000)) * ((36832635013 / 1000000000000000000))) + ((835306071 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13025) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((55219609 / 12500000000000000000) : ℝ) + ((835306071 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13025

namespace BstLean.Part266.Row13025
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13025 165 ∧
    0 ≤ (tableEnvelope C).f1 13025 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13025 165 ∧
    0 ≤ (tableEnvelope C).w1 13025 165 ∧ 0 ≤ (tableEnvelope C).w2 13025 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13025 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13025 165 ∧ 0 ≤ d.f1 13025 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13025 165 ∧ 0 ≤ d.w1 13025 165 ∧ 0 ≤ d.w2 13025 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13025 ≤ 2 * (228 / 100 : ℝ) / 13025 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13025 ≤ 2 * (370 / 100 : ℝ) / 13025 := by
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
    (completeRAData (tableEnvelope C) 13025 165).locationBound 13025 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13025 165).energyBound 13025 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13025 165) (d.f1 13025 165) d.f2 ≤
      32 * (((4302144571 / 1000000000000000000) : ℝ) + (1435268129 / 1000000000000000000) + (21560451 / 62500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13025 165) (d.w1 13025 165)
      (d.w2 13025 165) ≤
      32 * (((849681099 / 50000000000000000000) : ℝ) + (12090637 / 1000000000000000000) + (220880459 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13025 165) (d.f1 13025 165) d.f2 ≤
      ((4302144571 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4302144571 / 1000000000000000000)) * ((1435268129 / 1000000000000000000)) * (126 / 100) +
      2 * (((1435268129 / 1000000000000000000)) ^ 2 + 2 * ((4302144571 / 1000000000000000000)) * ((21560451 / 62500000000000000))) +
      6 * ((1435268129 / 1000000000000000000)) * ((21560451 / 62500000000000000)) * (126 / 100) + 8 * ((21560451 / 62500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13025 165) (d.f1 13025 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13025 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13025 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13025 165) (d.f1 13025 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13025 165) (d.w1 13025 165) (d.w2 13025 165)
  have hwexpr0 : 0 ≤ d.w0 13025 165 + d.w1 13025 165 * √(π / 2) +
      2 * d.w2 13025 165 + energyR16 13025 *
      radiusPolynomialRoot16 (d.w0 13025 165) (d.w1 13025 165) (d.w2 13025 165) := by
    positivity
  constructor
  · change (13025 : ℝ) ^ 8 * (mA 13025 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13025 165) (d.f1 13025 165) d.f2 + locationR16 13025 *
        radiusPolynomialRoot16 (d.f0 13025 165) (d.f1 13025 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13025 : ℝ) ^ 8 * (mA 13025 : ℝ) ^ 8 *
        ((((4302144571 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4302144571 / 1000000000000000000)) * ((1435268129 / 1000000000000000000)) * (126 / 100) +
          2 * (((1435268129 / 1000000000000000000)) ^ 2 + 2 * ((4302144571 / 1000000000000000000)) * ((21560451 / 62500000000000000))) +
          6 * ((1435268129 / 1000000000000000000)) * ((21560451 / 62500000000000000)) * (126 / 100) + 8 * ((21560451 / 62500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13025) *
          (32 * (((4302144571 / 1000000000000000000) : ℝ) + (1435268129 / 1000000000000000000) + (21560451 / 62500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13025 : ℝ) ^ 16 *
      (d.w0 13025 165 + d.w1 13025 165 * √(π / 2) + 2 * d.w2 13025 165 +
        energyR16 13025 * radiusPolynomialRoot16 (d.w0 13025 165) (d.w1 13025 165)
          (d.w2 13025 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13025 : ℝ) ^ 16 *
        (((849681099 / 50000000000000000000) : ℝ) + ((12090637 / 1000000000000000000)) * (126 / 100) + 2 * ((220880459 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13025) *
          (32 * (((849681099 / 50000000000000000000) : ℝ) + (12090637 / 1000000000000000000) + (220880459 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13025

/-! A coarse bound on the actual paper statistics constant at dimension 13026. -/
namespace BstLean.Part266.Row13026
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13024 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13024 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13024 128 ≤ (13278 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13278 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13026) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13026 : ℕ))
    (by norm_num : (13026 : ℕ) ≤ 16384)
  have ht : paperTail256 13026 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13026 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13026 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13026 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13026 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13026 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13024 128 * √(2 / (13026 : ℝ)) *
      (√(13026 : ℝ) + paperT0 13026 + paperTail256 13026) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13026 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13026 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13026 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13024 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13024 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13026 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13026

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13026
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13026 (61 / 100) 165 (17 / (100 * 13026)) (26 / (10 * 13026)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13026 (61 / 100) 165 (17 / (100 * 13026)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (220827567 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1356226439 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4173941679 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13026 / 13026 * (61 / 100)) ^ 4 * inverseRadius8 (13026 - 1) /
            envelopeGap 13026 (61 / 100) 165 (17 / (100 * 13026)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13026

namespace BstLean.Part266.Row13026
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13026 165 ≤ (4301316559 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13026 165 ≤ (2802719 / 1953125000000000)
  f2 : (tableEnvelope C).f2 ≤ (21556309 / 62500000000000000)
  w0 : (tableEnvelope C).w0 13026 165 ≤ (1698970359 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13026 165 ≤ (1208785023 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13026 165 ≤ (220829589 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (220827567 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (220827567 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1356226439 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4173941679 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((225787 / 62500000) : ℝ) ≤ √(17 / (100 * 13026) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13026) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (65673727 / 31250000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36826979771 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13026) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13026) ≤ (54284261 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13026) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13026 * (165 : ℝ) ^ 2 + 26 / (10 * 13026) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13026) : ℝ)) (tA 13026 * 165 ^ 2 + 26 / (10 * 13026)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((225787 / 62500000))) * ((220827567 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((225787 / 62500000)) ^ 3) * ((1356226439 / 1000000000000000000000000))) + ((4173941679 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((225787 / 62500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13026) : ℝ)) d.D d.V d.P (√(tA 13026) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((225787 / 62500000)) ^ 2 * (((65673727 / 31250000000000)) * ((36826979771 / 1000000000000000000)))) + ((4173941679 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13026) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((225787 / 62500000)) * ((220827567 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13026) : ℝ)) (tA 13026 * 165 ^ 2 + 26 / (10 * 13026)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((220827567 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((225787 / 62500000)) ^ 2) * ((1356226439 / 1000000000000000000000000)) + ((4173941679 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13026) : ℝ)) (√(26 / (10 * 13026) : ℝ)) d.D d.V d.P (√(tA 13026) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((225787 / 62500000)) * (((65673727 / 31250000000000)) * ((36826979771 / 1000000000000000000))) + ((4173941679 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13026) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((220827567 / 50000000000000000000) : ℝ) + ((4173941679 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13026

namespace BstLean.Part266.Row13026
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13026 165 ∧
    0 ≤ (tableEnvelope C).f1 13026 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13026 165 ∧
    0 ≤ (tableEnvelope C).w1 13026 165 ∧ 0 ≤ (tableEnvelope C).w2 13026 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13026 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13026 165 ∧ 0 ≤ d.f1 13026 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13026 165 ∧ 0 ≤ d.w1 13026 165 ∧ 0 ≤ d.w2 13026 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13026 ≤ 2 * (228 / 100 : ℝ) / 13026 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13026 ≤ 2 * (370 / 100 : ℝ) / 13026 := by
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
    (completeRAData (tableEnvelope C) 13026 165).locationBound 13026 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13026 165).energyBound 13026 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13026 165) (d.f1 13026 165) d.f2 ≤
      32 * (((4301316559 / 1000000000000000000) : ℝ) + (2802719 / 1953125000000000) + (21556309 / 62500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13026 165) (d.w1 13026 165)
      (d.w2 13026 165) ≤
      32 * (((1698970359 / 100000000000000000000) : ℝ) + (1208785023 / 100000000000000000000) + (220829589 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13026 165) (d.f1 13026 165) d.f2 ≤
      ((4301316559 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4301316559 / 1000000000000000000)) * ((2802719 / 1953125000000000)) * (126 / 100) +
      2 * (((2802719 / 1953125000000000)) ^ 2 + 2 * ((4301316559 / 1000000000000000000)) * ((21556309 / 62500000000000000))) +
      6 * ((2802719 / 1953125000000000)) * ((21556309 / 62500000000000000)) * (126 / 100) + 8 * ((21556309 / 62500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13026 165) (d.f1 13026 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13026 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13026 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13026 165) (d.f1 13026 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13026 165) (d.w1 13026 165) (d.w2 13026 165)
  have hwexpr0 : 0 ≤ d.w0 13026 165 + d.w1 13026 165 * √(π / 2) +
      2 * d.w2 13026 165 + energyR16 13026 *
      radiusPolynomialRoot16 (d.w0 13026 165) (d.w1 13026 165) (d.w2 13026 165) := by
    positivity
  constructor
  · change (13026 : ℝ) ^ 8 * (mA 13026 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13026 165) (d.f1 13026 165) d.f2 + locationR16 13026 *
        radiusPolynomialRoot16 (d.f0 13026 165) (d.f1 13026 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13026 : ℝ) ^ 8 * (mA 13026 : ℝ) ^ 8 *
        ((((4301316559 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4301316559 / 1000000000000000000)) * ((2802719 / 1953125000000000)) * (126 / 100) +
          2 * (((2802719 / 1953125000000000)) ^ 2 + 2 * ((4301316559 / 1000000000000000000)) * ((21556309 / 62500000000000000))) +
          6 * ((2802719 / 1953125000000000)) * ((21556309 / 62500000000000000)) * (126 / 100) + 8 * ((21556309 / 62500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13026) *
          (32 * (((4301316559 / 1000000000000000000) : ℝ) + (2802719 / 1953125000000000) + (21556309 / 62500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13026 : ℝ) ^ 16 *
      (d.w0 13026 165 + d.w1 13026 165 * √(π / 2) + 2 * d.w2 13026 165 +
        energyR16 13026 * radiusPolynomialRoot16 (d.w0 13026 165) (d.w1 13026 165)
          (d.w2 13026 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13026 : ℝ) ^ 16 *
        (((1698970359 / 100000000000000000000) : ℝ) + ((1208785023 / 100000000000000000000)) * (126 / 100) + 2 * ((220829589 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13026) *
          (32 * (((1698970359 / 100000000000000000000) : ℝ) + (1208785023 / 100000000000000000000) + (220829589 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13026

/-! A coarse bound on the actual paper statistics constant at dimension 13027. -/
namespace BstLean.Part266.Row13027
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13025 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13025 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13025 128 ≤ (13279 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13279 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13027) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13027 : ℕ))
    (by norm_num : (13027 : ℕ) ≤ 16384)
  have ht : paperTail256 13027 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13027 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13027 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13027 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13027 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13027 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13025 128 * √(2 / (13027 : ℝ)) *
      (√(13027 : ℝ) + paperT0 13027 + paperTail256 13027) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13027 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13027 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13027 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13025 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13025 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13027 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13027

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13027
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13027 (61 / 100) 165 (17 / (100 * 13027)) (26 / (10 * 13027)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13027 (61 / 100) 165 (17 / (100 * 13027)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (441553427 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (271162007 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (417135481 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13027 / 13027 * (61 / 100)) ^ 4 * inverseRadius8 (13027 - 1) /
            envelopeGap 13027 (61 / 100) 165 (17 / (100 * 13027)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13027

namespace BstLean.Part266.Row13027
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13027 165 ≤ (4300492259 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13027 165 ≤ (89669813 / 62500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (172417393 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13027 165 ≤ (1698579347 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13027 165 ≤ (1208506771 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13027 165 ≤ (110389367 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (441553427 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (441553427 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (271162007 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (417135481 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3612453 / 1000000000) : ℝ) ≤ √(17 / (100 * 13027) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13027) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2101317271 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36821325819 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13027) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13027) ≤ (27140047 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13027) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13027 * (165 : ℝ) ^ 2 + 26 / (10 * 13027) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13027) : ℝ)) (tA 13027 * 165 ^ 2 + 26 / (10 * 13027)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3612453 / 1000000000))) * ((441553427 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3612453 / 1000000000)) ^ 3) * ((271162007 / 200000000000000000000000))) + ((417135481 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3612453 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13027) : ℝ)) d.D d.V d.P (√(tA 13027) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3612453 / 1000000000)) ^ 2 * (((2101317271 / 1000000000000000)) * ((36821325819 / 1000000000000000000)))) + ((417135481 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13027) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3612453 / 1000000000)) * ((441553427 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13027) : ℝ)) (tA 13027 * 165 ^ 2 + 26 / (10 * 13027)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((441553427 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3612453 / 1000000000)) ^ 2) * ((271162007 / 200000000000000000000000)) + ((417135481 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13027) : ℝ)) (√(26 / (10 * 13027) : ℝ)) d.D d.V d.P (√(tA 13027) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3612453 / 1000000000)) * (((2101317271 / 1000000000000000)) * ((36821325819 / 1000000000000000000))) + ((417135481 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13027) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((441553427 / 100000000000000000000) : ℝ) + ((417135481 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13027

namespace BstLean.Part266.Row13027
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13027 165 ∧
    0 ≤ (tableEnvelope C).f1 13027 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13027 165 ∧
    0 ≤ (tableEnvelope C).w1 13027 165 ∧ 0 ≤ (tableEnvelope C).w2 13027 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13027 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13027 165 ∧ 0 ≤ d.f1 13027 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13027 165 ∧ 0 ≤ d.w1 13027 165 ∧ 0 ≤ d.w2 13027 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13027 ≤ 2 * (228 / 100 : ℝ) / 13027 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13027 ≤ 2 * (370 / 100 : ℝ) / 13027 := by
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
    (completeRAData (tableEnvelope C) 13027 165).locationBound 13027 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13027 165).energyBound 13027 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13027 165) (d.f1 13027 165) d.f2 ≤
      32 * (((4300492259 / 1000000000000000000) : ℝ) + (89669813 / 62500000000000000) + (172417393 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13027 165) (d.w1 13027 165)
      (d.w2 13027 165) ≤
      32 * (((1698579347 / 100000000000000000000) : ℝ) + (1208506771 / 100000000000000000000) + (110389367 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13027 165) (d.f1 13027 165) d.f2 ≤
      ((4300492259 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4300492259 / 1000000000000000000)) * ((89669813 / 62500000000000000)) * (126 / 100) +
      2 * (((89669813 / 62500000000000000)) ^ 2 + 2 * ((4300492259 / 1000000000000000000)) * ((172417393 / 500000000000000000))) +
      6 * ((89669813 / 62500000000000000)) * ((172417393 / 500000000000000000)) * (126 / 100) + 8 * ((172417393 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13027 165) (d.f1 13027 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13027 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13027 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13027 165) (d.f1 13027 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13027 165) (d.w1 13027 165) (d.w2 13027 165)
  have hwexpr0 : 0 ≤ d.w0 13027 165 + d.w1 13027 165 * √(π / 2) +
      2 * d.w2 13027 165 + energyR16 13027 *
      radiusPolynomialRoot16 (d.w0 13027 165) (d.w1 13027 165) (d.w2 13027 165) := by
    positivity
  constructor
  · change (13027 : ℝ) ^ 8 * (mA 13027 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13027 165) (d.f1 13027 165) d.f2 + locationR16 13027 *
        radiusPolynomialRoot16 (d.f0 13027 165) (d.f1 13027 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13027 : ℝ) ^ 8 * (mA 13027 : ℝ) ^ 8 *
        ((((4300492259 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4300492259 / 1000000000000000000)) * ((89669813 / 62500000000000000)) * (126 / 100) +
          2 * (((89669813 / 62500000000000000)) ^ 2 + 2 * ((4300492259 / 1000000000000000000)) * ((172417393 / 500000000000000000))) +
          6 * ((89669813 / 62500000000000000)) * ((172417393 / 500000000000000000)) * (126 / 100) + 8 * ((172417393 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13027) *
          (32 * (((4300492259 / 1000000000000000000) : ℝ) + (89669813 / 62500000000000000) + (172417393 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13027 : ℝ) ^ 16 *
      (d.w0 13027 165 + d.w1 13027 165 * √(π / 2) + 2 * d.w2 13027 165 +
        energyR16 13027 * radiusPolynomialRoot16 (d.w0 13027 165) (d.w1 13027 165)
          (d.w2 13027 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13027 : ℝ) ^ 16 *
        (((1698579347 / 100000000000000000000) : ℝ) + ((1208506771 / 100000000000000000000)) * (126 / 100) + 2 * ((110389367 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13027) *
          (32 * (((1698579347 / 100000000000000000000) : ℝ) + (1208506771 / 100000000000000000000) + (110389367 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13027

/-! A coarse bound on the actual paper statistics constant at dimension 13028. -/
namespace BstLean.Part266.Row13028
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13026 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13026 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13026 128 ≤ (13280 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13280 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13028) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13028 : ℕ))
    (by norm_num : (13028 : ℕ) ≤ 16384)
  have ht : paperTail256 13028 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13028 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13028 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13028 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13028 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13028 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13026 128 * √(2 / (13028 : ℝ)) *
      (√(13028 : ℝ) + paperT0 13028 + paperTail256 13028) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13028 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13028 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13028 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13026 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13026 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13028 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13028

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13028
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13028 (61 / 100) 165 (17 / (100 * 13028)) (26 / (10 * 13028)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13028 (61 / 100) 165 (17 / (100 * 13028)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (55181469 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1355393791 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2084384873 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13028 / 13028 * (61 / 100)) ^ 4 * inverseRadius8 (13028 - 1) /
            envelopeGap 13028 (61 / 100) 165 (17 / (100 * 13028)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13028

namespace BstLean.Part266.Row13028
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13028 165 ≤ (4299668237 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13028 165 ≤ (57377679 / 40000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (43096081 / 125000000000000000)
  w0 : (tableEnvelope C).w0 13028 165 ≤ (1698188467 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13028 165 ≤ (120822861 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 13028 165 ≤ (441455791 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (55181469 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (55181469 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1355393791 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2084384873 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1806157 / 500000000) : ℝ) ≤ √(17 / (100 * 13028) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13028) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (84043013 / 40000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36815673171 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13028) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13028) ≤ (21710371 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13028) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13028 * (165 : ℝ) ^ 2 + 26 / (10 * 13028) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13028) : ℝ)) (tA 13028 * 165 ^ 2 + 26 / (10 * 13028)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1806157 / 500000000))) * ((55181469 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1806157 / 500000000)) ^ 3) * ((1355393791 / 1000000000000000000000000))) + ((2084384873 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1806157 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13028) : ℝ)) d.D d.V d.P (√(tA 13028) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1806157 / 500000000)) ^ 2 * (((84043013 / 40000000000000)) * ((36815673171 / 1000000000000000000)))) + ((2084384873 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13028) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1806157 / 500000000)) * ((55181469 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13028) : ℝ)) (tA 13028 * 165 ^ 2 + 26 / (10 * 13028)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((55181469 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1806157 / 500000000)) ^ 2) * ((1355393791 / 1000000000000000000000000)) + ((2084384873 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13028) : ℝ)) (√(26 / (10 * 13028) : ℝ)) d.D d.V d.P (√(tA 13028) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1806157 / 500000000)) * (((84043013 / 40000000000000)) * ((36815673171 / 1000000000000000000))) + ((2084384873 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13028) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((55181469 / 12500000000000000000) : ℝ) + ((2084384873 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13028

namespace BstLean.Part266.Row13028
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13028 165 ∧
    0 ≤ (tableEnvelope C).f1 13028 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13028 165 ∧
    0 ≤ (tableEnvelope C).w1 13028 165 ∧ 0 ≤ (tableEnvelope C).w2 13028 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13028 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13028 165 ∧ 0 ≤ d.f1 13028 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13028 165 ∧ 0 ≤ d.w1 13028 165 ∧ 0 ≤ d.w2 13028 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13028 ≤ 2 * (228 / 100 : ℝ) / 13028 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13028 ≤ 2 * (370 / 100 : ℝ) / 13028 := by
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
    (completeRAData (tableEnvelope C) 13028 165).locationBound 13028 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13028 165).energyBound 13028 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13028 165) (d.f1 13028 165) d.f2 ≤
      32 * (((4299668237 / 1000000000000000000) : ℝ) + (57377679 / 40000000000000000) + (43096081 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13028 165) (d.w1 13028 165)
      (d.w2 13028 165) ≤
      32 * (((1698188467 / 100000000000000000000) : ℝ) + (120822861 / 10000000000000000000) + (441455791 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13028 165) (d.f1 13028 165) d.f2 ≤
      ((4299668237 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4299668237 / 1000000000000000000)) * ((57377679 / 40000000000000000)) * (126 / 100) +
      2 * (((57377679 / 40000000000000000)) ^ 2 + 2 * ((4299668237 / 1000000000000000000)) * ((43096081 / 125000000000000000))) +
      6 * ((57377679 / 40000000000000000)) * ((43096081 / 125000000000000000)) * (126 / 100) + 8 * ((43096081 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13028 165) (d.f1 13028 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13028 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13028 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13028 165) (d.f1 13028 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13028 165) (d.w1 13028 165) (d.w2 13028 165)
  have hwexpr0 : 0 ≤ d.w0 13028 165 + d.w1 13028 165 * √(π / 2) +
      2 * d.w2 13028 165 + energyR16 13028 *
      radiusPolynomialRoot16 (d.w0 13028 165) (d.w1 13028 165) (d.w2 13028 165) := by
    positivity
  constructor
  · change (13028 : ℝ) ^ 8 * (mA 13028 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13028 165) (d.f1 13028 165) d.f2 + locationR16 13028 *
        radiusPolynomialRoot16 (d.f0 13028 165) (d.f1 13028 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13028 : ℝ) ^ 8 * (mA 13028 : ℝ) ^ 8 *
        ((((4299668237 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4299668237 / 1000000000000000000)) * ((57377679 / 40000000000000000)) * (126 / 100) +
          2 * (((57377679 / 40000000000000000)) ^ 2 + 2 * ((4299668237 / 1000000000000000000)) * ((43096081 / 125000000000000000))) +
          6 * ((57377679 / 40000000000000000)) * ((43096081 / 125000000000000000)) * (126 / 100) + 8 * ((43096081 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13028) *
          (32 * (((4299668237 / 1000000000000000000) : ℝ) + (57377679 / 40000000000000000) + (43096081 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13028 : ℝ) ^ 16 *
      (d.w0 13028 165 + d.w1 13028 165 * √(π / 2) + 2 * d.w2 13028 165 +
        energyR16 13028 * radiusPolynomialRoot16 (d.w0 13028 165) (d.w1 13028 165)
          (d.w2 13028 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13028 : ℝ) ^ 16 *
        (((1698188467 / 100000000000000000000) : ℝ) + ((120822861 / 10000000000000000000)) * (126 / 100) + 2 * ((441455791 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13028) *
          (32 * (((1698188467 / 100000000000000000000) : ℝ) + (120822861 / 10000000000000000000) + (441455791 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13028

/-! A coarse bound on the actual paper statistics constant at dimension 13029. -/
namespace BstLean.Part266.Row13029
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13027 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13027 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13027 128 ≤ (13281 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13281 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13029) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13029 : ℕ))
    (by norm_num : (13029 : ℕ) ≤ 16384)
  have ht : paperTail256 13029 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13029 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13029 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13029 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13029 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13029 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13027 128 * √(2 / (13029 : ℝ)) *
      (√(13029 : ℝ) + paperT0 13029 + paperTail256 13029) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13029 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13029 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13029 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13027 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13027 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13029 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13029

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13029
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13029 (61 / 100) 165 (17 / (100 * 13029)) (26 / (10 * 13029)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13029 (61 / 100) 165 (17 / (100 * 13029)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (110337527 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1354977707 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2083093243 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13029 / 13029 * (61 / 100)) ^ 4 * inverseRadius8 (13029 - 1) /
            envelopeGap 13029 (61 / 100) 165 (17 / (100 * 13029)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13029

namespace BstLean.Part266.Row13029
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13029 165 ≤ (859768211 / 200000000000000000)
  f1 : (tableEnvelope C).f1 13029 165 ≤ (286833247 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (172351217 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13029 165 ≤ (848898511 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13029 165 ≤ (603975103 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13029 165 ≤ (13792317 / 3125000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (110337527 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (110337527 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1354977707 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2083093243 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((225761 / 62500000) : ℝ) ≤ √(17 / (100 * 13029) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13029) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1050416713 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36810021829 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13029) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13029) ≤ (27135881 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13029) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13029 * (165 : ℝ) ^ 2 + 26 / (10 * 13029) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13029) : ℝ)) (tA 13029 * 165 ^ 2 + 26 / (10 * 13029)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((225761 / 62500000))) * ((110337527 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((225761 / 62500000)) ^ 3) * ((1354977707 / 1000000000000000000000000))) + ((2083093243 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((225761 / 62500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13029) : ℝ)) d.D d.V d.P (√(tA 13029) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((225761 / 62500000)) ^ 2 * (((1050416713 / 500000000000000)) * ((36810021829 / 1000000000000000000)))) + ((2083093243 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13029) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((225761 / 62500000)) * ((110337527 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13029) : ℝ)) (tA 13029 * 165 ^ 2 + 26 / (10 * 13029)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((110337527 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((225761 / 62500000)) ^ 2) * ((1354977707 / 1000000000000000000000000)) + ((2083093243 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13029) : ℝ)) (√(26 / (10 * 13029) : ℝ)) d.D d.V d.P (√(tA 13029) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((225761 / 62500000)) * (((1050416713 / 500000000000000)) * ((36810021829 / 1000000000000000000))) + ((2083093243 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13029) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((110337527 / 25000000000000000000) : ℝ) + ((2083093243 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13029

namespace BstLean.Part266.Row13029
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13029 165 ∧
    0 ≤ (tableEnvelope C).f1 13029 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13029 165 ∧
    0 ≤ (tableEnvelope C).w1 13029 165 ∧ 0 ≤ (tableEnvelope C).w2 13029 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13029 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13029 165 ∧ 0 ≤ d.f1 13029 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13029 165 ∧ 0 ≤ d.w1 13029 165 ∧ 0 ≤ d.w2 13029 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13029 ≤ 2 * (228 / 100 : ℝ) / 13029 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13029 ≤ 2 * (370 / 100 : ℝ) / 13029 := by
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
    (completeRAData (tableEnvelope C) 13029 165).locationBound 13029 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13029 165).energyBound 13029 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13029 165) (d.f1 13029 165) d.f2 ≤
      32 * (((859768211 / 200000000000000000) : ℝ) + (286833247 / 200000000000000000) + (172351217 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13029 165) (d.w1 13029 165)
      (d.w2 13029 165) ≤
      32 * (((848898511 / 50000000000000000000) : ℝ) + (603975103 / 50000000000000000000) + (13792317 / 3125000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13029 165) (d.f1 13029 165) d.f2 ≤
      ((859768211 / 200000000000000000) : ℝ) ^ 2 + 2 * ((859768211 / 200000000000000000)) * ((286833247 / 200000000000000000)) * (126 / 100) +
      2 * (((286833247 / 200000000000000000)) ^ 2 + 2 * ((859768211 / 200000000000000000)) * ((172351217 / 500000000000000000))) +
      6 * ((286833247 / 200000000000000000)) * ((172351217 / 500000000000000000)) * (126 / 100) + 8 * ((172351217 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13029 165) (d.f1 13029 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13029 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13029 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13029 165) (d.f1 13029 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13029 165) (d.w1 13029 165) (d.w2 13029 165)
  have hwexpr0 : 0 ≤ d.w0 13029 165 + d.w1 13029 165 * √(π / 2) +
      2 * d.w2 13029 165 + energyR16 13029 *
      radiusPolynomialRoot16 (d.w0 13029 165) (d.w1 13029 165) (d.w2 13029 165) := by
    positivity
  constructor
  · change (13029 : ℝ) ^ 8 * (mA 13029 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13029 165) (d.f1 13029 165) d.f2 + locationR16 13029 *
        radiusPolynomialRoot16 (d.f0 13029 165) (d.f1 13029 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13029 : ℝ) ^ 8 * (mA 13029 : ℝ) ^ 8 *
        ((((859768211 / 200000000000000000) : ℝ) ^ 2 + 2 * ((859768211 / 200000000000000000)) * ((286833247 / 200000000000000000)) * (126 / 100) +
          2 * (((286833247 / 200000000000000000)) ^ 2 + 2 * ((859768211 / 200000000000000000)) * ((172351217 / 500000000000000000))) +
          6 * ((286833247 / 200000000000000000)) * ((172351217 / 500000000000000000)) * (126 / 100) + 8 * ((172351217 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13029) *
          (32 * (((859768211 / 200000000000000000) : ℝ) + (286833247 / 200000000000000000) + (172351217 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13029 : ℝ) ^ 16 *
      (d.w0 13029 165 + d.w1 13029 165 * √(π / 2) + 2 * d.w2 13029 165 +
        energyR16 13029 * radiusPolynomialRoot16 (d.w0 13029 165) (d.w1 13029 165)
          (d.w2 13029 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13029 : ℝ) ^ 16 *
        (((848898511 / 50000000000000000000) : ℝ) + ((603975103 / 50000000000000000000)) * (126 / 100) + 2 * ((13792317 / 3125000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13029) *
          (32 * (((848898511 / 50000000000000000000) : ℝ) + (603975103 / 50000000000000000000) + (13792317 / 3125000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13029

/-! A coarse bound on the actual paper statistics constant at dimension 13030. -/
namespace BstLean.Part266.Row13030
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13028 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13028 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13028 128 ≤ (13282 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13282 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13030) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13030 : ℕ))
    (by norm_num : (13030 : ℕ) ≤ 16384)
  have ht : paperTail256 13030 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13030 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13030 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13030 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13030 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13030 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13028 128 * √(2 / (13030 : ℝ)) *
      (√(13030 : ℝ) + paperT0 13030 + paperTail256 13030) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13030 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13030 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13030 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13028 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13028 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13030 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13030

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13030
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13030 (61 / 100) 165 (17 / (100 * 13030)) (26 / (10 * 13030)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13030 (61 / 100) 165 (17 / (100 * 13030)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (88249699 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1354561783 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4163605029 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13030 / 13030 * (61 / 100)) ^ 4 * inverseRadius8 (13030 - 1) /
            envelopeGap 13030 (61 / 100) 165 (17 / (100 * 13030)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13030

namespace BstLean.Part266.Row13030
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13030 165 ≤ (4298017587 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13030 165 ≤ (11471131 / 8000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (172318167 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13030 165 ≤ (424351601 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 13030 165 ≤ (603836113 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13030 165 ≤ (441252529 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (88249699 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (88249699 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1354561783 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4163605029 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3612037 / 1000000000) : ℝ) ≤ √(17 / (100 * 13030) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13030) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (525147893 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (2300273237 / 62500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13030) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13030) ≤ (108535193 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13030) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13030 * (165 : ℝ) ^ 2 + 26 / (10 * 13030) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13030) : ℝ)) (tA 13030 * 165 ^ 2 + 26 / (10 * 13030)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3612037 / 1000000000))) * ((88249699 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3612037 / 1000000000)) ^ 3) * ((1354561783 / 1000000000000000000000000))) + ((4163605029 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3612037 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13030) : ℝ)) d.D d.V d.P (√(tA 13030) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3612037 / 1000000000)) ^ 2 * (((525147893 / 250000000000000)) * ((2300273237 / 62500000000000000)))) + ((4163605029 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13030) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3612037 / 1000000000)) * ((88249699 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13030) : ℝ)) (tA 13030 * 165 ^ 2 + 26 / (10 * 13030)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((88249699 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3612037 / 1000000000)) ^ 2) * ((1354561783 / 1000000000000000000000000)) + ((4163605029 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13030) : ℝ)) (√(26 / (10 * 13030) : ℝ)) d.D d.V d.P (√(tA 13030) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3612037 / 1000000000)) * (((525147893 / 250000000000000)) * ((2300273237 / 62500000000000000))) + ((4163605029 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13030) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((88249699 / 20000000000000000000) : ℝ) + ((4163605029 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13030

namespace BstLean.Part266.Row13030
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13030 165 ∧
    0 ≤ (tableEnvelope C).f1 13030 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13030 165 ∧
    0 ≤ (tableEnvelope C).w1 13030 165 ∧ 0 ≤ (tableEnvelope C).w2 13030 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13030 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13030 165 ∧ 0 ≤ d.f1 13030 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13030 165 ∧ 0 ≤ d.w1 13030 165 ∧ 0 ≤ d.w2 13030 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13030 ≤ 2 * (228 / 100 : ℝ) / 13030 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13030 ≤ 2 * (370 / 100 : ℝ) / 13030 := by
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
    (completeRAData (tableEnvelope C) 13030 165).locationBound 13030 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13030 165).energyBound 13030 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13030 165) (d.f1 13030 165) d.f2 ≤
      32 * (((4298017587 / 1000000000000000000) : ℝ) + (11471131 / 8000000000000000) + (172318167 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13030 165) (d.w1 13030 165)
      (d.w2 13030 165) ≤
      32 * (((424351601 / 25000000000000000000) : ℝ) + (603836113 / 50000000000000000000) + (441252529 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13030 165) (d.f1 13030 165) d.f2 ≤
      ((4298017587 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4298017587 / 1000000000000000000)) * ((11471131 / 8000000000000000)) * (126 / 100) +
      2 * (((11471131 / 8000000000000000)) ^ 2 + 2 * ((4298017587 / 1000000000000000000)) * ((172318167 / 500000000000000000))) +
      6 * ((11471131 / 8000000000000000)) * ((172318167 / 500000000000000000)) * (126 / 100) + 8 * ((172318167 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13030 165) (d.f1 13030 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13030 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13030 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13030 165) (d.f1 13030 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13030 165) (d.w1 13030 165) (d.w2 13030 165)
  have hwexpr0 : 0 ≤ d.w0 13030 165 + d.w1 13030 165 * √(π / 2) +
      2 * d.w2 13030 165 + energyR16 13030 *
      radiusPolynomialRoot16 (d.w0 13030 165) (d.w1 13030 165) (d.w2 13030 165) := by
    positivity
  constructor
  · change (13030 : ℝ) ^ 8 * (mA 13030 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13030 165) (d.f1 13030 165) d.f2 + locationR16 13030 *
        radiusPolynomialRoot16 (d.f0 13030 165) (d.f1 13030 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13030 : ℝ) ^ 8 * (mA 13030 : ℝ) ^ 8 *
        ((((4298017587 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4298017587 / 1000000000000000000)) * ((11471131 / 8000000000000000)) * (126 / 100) +
          2 * (((11471131 / 8000000000000000)) ^ 2 + 2 * ((4298017587 / 1000000000000000000)) * ((172318167 / 500000000000000000))) +
          6 * ((11471131 / 8000000000000000)) * ((172318167 / 500000000000000000)) * (126 / 100) + 8 * ((172318167 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13030) *
          (32 * (((4298017587 / 1000000000000000000) : ℝ) + (11471131 / 8000000000000000) + (172318167 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13030 : ℝ) ^ 16 *
      (d.w0 13030 165 + d.w1 13030 165 * √(π / 2) + 2 * d.w2 13030 165 +
        energyR16 13030 * radiusPolynomialRoot16 (d.w0 13030 165) (d.w1 13030 165)
          (d.w2 13030 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13030 : ℝ) ^ 16 *
        (((424351601 / 25000000000000000000) : ℝ) + ((603836113 / 50000000000000000000)) * (126 / 100) + 2 * ((441252529 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13030) *
          (32 * (((424351601 / 25000000000000000000) : ℝ) + (603836113 / 50000000000000000000) + (441252529 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13030

/-! A coarse bound on the actual paper statistics constant at dimension 13031. -/
namespace BstLean.Part266.Row13031
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13029 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13029 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13029 128 ≤ (13283 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13283 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13031) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13031 : ℕ))
    (by norm_num : (13031 : ℕ) ≤ 16384)
  have ht : paperTail256 13031 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13031 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13031 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13031 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13031 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13031 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13029 128 * √(2 / (13031 : ℝ)) *
      (√(13031 : ℝ) + paperT0 13031 + paperTail256 13031) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13031 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13031 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13031 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13029 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13029 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13031 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13031

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13031
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13031 (61 / 100) 165 (17 / (100 * 13031)) (26 / (10 * 13031)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13031 (61 / 100) 165 (17 / (100 * 13031)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (441146913 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (677073009 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4161025373 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13031 / 13031 * (61 / 100)) ^ 4 * inverseRadius8 (13031 - 1) /
            envelopeGap 13031 (61 / 100) 165 (17 / (100 * 13031)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13031

namespace BstLean.Part266.Row13031
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13031 165 ≤ (537149299 / 125000000000000000)
  f1 : (tableEnvelope C).f1 13031 165 ≤ (1433616601 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (172285127 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13031 165 ≤ (424253979 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 13031 165 ≤ (37731073 / 3125000000000000000)
  w2 : (tableEnvelope C).w2 13031 165 ≤ (13785967 / 3125000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (441146913 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (441146913 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (677073009 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4161025373 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1805949 / 500000000) : ℝ) ≤ √(17 / (100 * 13031) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13031) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (525087441 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36798723049 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13031) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13031) ≤ (6782929 / 62500000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13031) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13031 * (165 : ℝ) ^ 2 + 26 / (10 * 13031) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13031) : ℝ)) (tA 13031 * 165 ^ 2 + 26 / (10 * 13031)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1805949 / 500000000))) * ((441146913 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1805949 / 500000000)) ^ 3) * ((677073009 / 500000000000000000000000))) + ((4161025373 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1805949 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13031) : ℝ)) d.D d.V d.P (√(tA 13031) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1805949 / 500000000)) ^ 2 * (((525087441 / 250000000000000)) * ((36798723049 / 1000000000000000000)))) + ((4161025373 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13031) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1805949 / 500000000)) * ((441146913 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13031) : ℝ)) (tA 13031 * 165 ^ 2 + 26 / (10 * 13031)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((441146913 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1805949 / 500000000)) ^ 2) * ((677073009 / 500000000000000000000000)) + ((4161025373 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13031) : ℝ)) (√(26 / (10 * 13031) : ℝ)) d.D d.V d.P (√(tA 13031) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1805949 / 500000000)) * (((525087441 / 250000000000000)) * ((36798723049 / 1000000000000000000))) + ((4161025373 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13031) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((441146913 / 100000000000000000000) : ℝ) + ((4161025373 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13031

namespace BstLean.Part266.Row13031
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13031 165 ∧
    0 ≤ (tableEnvelope C).f1 13031 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13031 165 ∧
    0 ≤ (tableEnvelope C).w1 13031 165 ∧ 0 ≤ (tableEnvelope C).w2 13031 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13031 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13031 165 ∧ 0 ≤ d.f1 13031 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13031 165 ∧ 0 ≤ d.w1 13031 165 ∧ 0 ≤ d.w2 13031 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13031 ≤ 2 * (228 / 100 : ℝ) / 13031 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13031 ≤ 2 * (370 / 100 : ℝ) / 13031 := by
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
    (completeRAData (tableEnvelope C) 13031 165).locationBound 13031 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13031 165).energyBound 13031 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13031 165) (d.f1 13031 165) d.f2 ≤
      32 * (((537149299 / 125000000000000000) : ℝ) + (1433616601 / 1000000000000000000) + (172285127 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13031 165) (d.w1 13031 165)
      (d.w2 13031 165) ≤
      32 * (((424253979 / 25000000000000000000) : ℝ) + (37731073 / 3125000000000000000) + (13785967 / 3125000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13031 165) (d.f1 13031 165) d.f2 ≤
      ((537149299 / 125000000000000000) : ℝ) ^ 2 + 2 * ((537149299 / 125000000000000000)) * ((1433616601 / 1000000000000000000)) * (126 / 100) +
      2 * (((1433616601 / 1000000000000000000)) ^ 2 + 2 * ((537149299 / 125000000000000000)) * ((172285127 / 500000000000000000))) +
      6 * ((1433616601 / 1000000000000000000)) * ((172285127 / 500000000000000000)) * (126 / 100) + 8 * ((172285127 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13031 165) (d.f1 13031 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13031 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13031 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13031 165) (d.f1 13031 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13031 165) (d.w1 13031 165) (d.w2 13031 165)
  have hwexpr0 : 0 ≤ d.w0 13031 165 + d.w1 13031 165 * √(π / 2) +
      2 * d.w2 13031 165 + energyR16 13031 *
      radiusPolynomialRoot16 (d.w0 13031 165) (d.w1 13031 165) (d.w2 13031 165) := by
    positivity
  constructor
  · change (13031 : ℝ) ^ 8 * (mA 13031 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13031 165) (d.f1 13031 165) d.f2 + locationR16 13031 *
        radiusPolynomialRoot16 (d.f0 13031 165) (d.f1 13031 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13031 : ℝ) ^ 8 * (mA 13031 : ℝ) ^ 8 *
        ((((537149299 / 125000000000000000) : ℝ) ^ 2 + 2 * ((537149299 / 125000000000000000)) * ((1433616601 / 1000000000000000000)) * (126 / 100) +
          2 * (((1433616601 / 1000000000000000000)) ^ 2 + 2 * ((537149299 / 125000000000000000)) * ((172285127 / 500000000000000000))) +
          6 * ((1433616601 / 1000000000000000000)) * ((172285127 / 500000000000000000)) * (126 / 100) + 8 * ((172285127 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13031) *
          (32 * (((537149299 / 125000000000000000) : ℝ) + (1433616601 / 1000000000000000000) + (172285127 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13031 : ℝ) ^ 16 *
      (d.w0 13031 165 + d.w1 13031 165 * √(π / 2) + 2 * d.w2 13031 165 +
        energyR16 13031 * radiusPolynomialRoot16 (d.w0 13031 165) (d.w1 13031 165)
          (d.w2 13031 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13031 : ℝ) ^ 16 *
        (((424253979 / 25000000000000000000) : ℝ) + ((37731073 / 3125000000000000000)) * (126 / 100) + 2 * ((13785967 / 3125000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13031) *
          (32 * (((424253979 / 25000000000000000000) : ℝ) + (37731073 / 3125000000000000000) + (13785967 / 3125000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13031

/-! A coarse bound on the actual paper statistics constant at dimension 13032. -/
namespace BstLean.Part266.Row13032
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13030 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13030 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13030 128 ≤ (13284 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13284 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13032) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13032 : ℕ))
    (by norm_num : (13032 : ℕ) ≤ 16384)
  have ht : paperTail256 13032 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13032 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13032 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13032 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13032 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13032 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13030 128 * √(2 / (13032 : ℝ)) *
      (√(13032 : ℝ) + paperT0 13032 + paperTail256 13032) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13032 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13032 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13032 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13030 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13030 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13032 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13032

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13032
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13032 (61 / 100) 165 (17 / (100 * 13032)) (26 / (10 * 13032)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13032 (61 / 100) 165 (17 / (100 * 13032)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (220522681 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1353730413 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4158447517 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13032 / 13032 * (61 / 100)) ^ 4 * inverseRadius8 (13032 - 1) /
            envelopeGap 13032 (61 / 100) 165 (17 / (100 * 13032)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13032

namespace BstLean.Part266.Row13032
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13032 165 ≤ (4296368041 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13032 165 ≤ (1433341119 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (344504097 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13032 165 ≤ (339324973 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 13032 165 ≤ (1207116203 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13032 165 ≤ (441049391 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (220522681 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (220522681 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1353730413 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4158447517 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((45147 / 12500000) : ℝ) ≤ √(17 / (100 * 13032) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13032) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1050054001 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36793075613 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13032) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13032) ≤ (108518537 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13032) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13032 * (165 : ℝ) ^ 2 + 26 / (10 * 13032) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13032) : ℝ)) (tA 13032 * 165 ^ 2 + 26 / (10 * 13032)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((45147 / 12500000))) * ((220522681 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((45147 / 12500000)) ^ 3) * ((1353730413 / 1000000000000000000000000))) + ((4158447517 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((45147 / 12500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13032) : ℝ)) d.D d.V d.P (√(tA 13032) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((45147 / 12500000)) ^ 2 * (((1050054001 / 500000000000000)) * ((36793075613 / 1000000000000000000)))) + ((4158447517 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13032) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((45147 / 12500000)) * ((220522681 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13032) : ℝ)) (tA 13032 * 165 ^ 2 + 26 / (10 * 13032)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((220522681 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((45147 / 12500000)) ^ 2) * ((1353730413 / 1000000000000000000000000)) + ((4158447517 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13032) : ℝ)) (√(26 / (10 * 13032) : ℝ)) d.D d.V d.P (√(tA 13032) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((45147 / 12500000)) * (((1050054001 / 500000000000000)) * ((36793075613 / 1000000000000000000))) + ((4158447517 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13032) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((220522681 / 50000000000000000000) : ℝ) + ((4158447517 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13032

namespace BstLean.Part266.Row13032
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13032 165 ∧
    0 ≤ (tableEnvelope C).f1 13032 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13032 165 ∧
    0 ≤ (tableEnvelope C).w1 13032 165 ∧ 0 ≤ (tableEnvelope C).w2 13032 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13032 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13032 165 ∧ 0 ≤ d.f1 13032 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13032 165 ∧ 0 ≤ d.w1 13032 165 ∧ 0 ≤ d.w2 13032 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13032 ≤ 2 * (228 / 100 : ℝ) / 13032 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13032 ≤ 2 * (370 / 100 : ℝ) / 13032 := by
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
    (completeRAData (tableEnvelope C) 13032 165).locationBound 13032 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13032 165).energyBound 13032 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13032 165) (d.f1 13032 165) d.f2 ≤
      32 * (((4296368041 / 1000000000000000000) : ℝ) + (1433341119 / 1000000000000000000) + (344504097 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13032 165) (d.w1 13032 165)
      (d.w2 13032 165) ≤
      32 * (((339324973 / 20000000000000000000) : ℝ) + (1207116203 / 100000000000000000000) + (441049391 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13032 165) (d.f1 13032 165) d.f2 ≤
      ((4296368041 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4296368041 / 1000000000000000000)) * ((1433341119 / 1000000000000000000)) * (126 / 100) +
      2 * (((1433341119 / 1000000000000000000)) ^ 2 + 2 * ((4296368041 / 1000000000000000000)) * ((344504097 / 1000000000000000000))) +
      6 * ((1433341119 / 1000000000000000000)) * ((344504097 / 1000000000000000000)) * (126 / 100) + 8 * ((344504097 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13032 165) (d.f1 13032 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13032 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13032 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13032 165) (d.f1 13032 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13032 165) (d.w1 13032 165) (d.w2 13032 165)
  have hwexpr0 : 0 ≤ d.w0 13032 165 + d.w1 13032 165 * √(π / 2) +
      2 * d.w2 13032 165 + energyR16 13032 *
      radiusPolynomialRoot16 (d.w0 13032 165) (d.w1 13032 165) (d.w2 13032 165) := by
    positivity
  constructor
  · change (13032 : ℝ) ^ 8 * (mA 13032 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13032 165) (d.f1 13032 165) d.f2 + locationR16 13032 *
        radiusPolynomialRoot16 (d.f0 13032 165) (d.f1 13032 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13032 : ℝ) ^ 8 * (mA 13032 : ℝ) ^ 8 *
        ((((4296368041 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4296368041 / 1000000000000000000)) * ((1433341119 / 1000000000000000000)) * (126 / 100) +
          2 * (((1433341119 / 1000000000000000000)) ^ 2 + 2 * ((4296368041 / 1000000000000000000)) * ((344504097 / 1000000000000000000))) +
          6 * ((1433341119 / 1000000000000000000)) * ((344504097 / 1000000000000000000)) * (126 / 100) + 8 * ((344504097 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13032) *
          (32 * (((4296368041 / 1000000000000000000) : ℝ) + (1433341119 / 1000000000000000000) + (344504097 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13032 : ℝ) ^ 16 *
      (d.w0 13032 165 + d.w1 13032 165 * √(π / 2) + 2 * d.w2 13032 165 +
        energyR16 13032 * radiusPolynomialRoot16 (d.w0 13032 165) (d.w1 13032 165)
          (d.w2 13032 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13032 : ℝ) ^ 16 *
        (((339324973 / 20000000000000000000) : ℝ) + ((1207116203 / 100000000000000000000)) * (126 / 100) + 2 * ((441049391 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13032) *
          (32 * (((339324973 / 20000000000000000000) : ℝ) + (1207116203 / 100000000000000000000) + (441049391 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13032

/-! A coarse bound on the actual paper statistics constant at dimension 13033. -/
namespace BstLean.Part266.Row13033
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13031 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13031 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13031 128 ≤ (13285 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13285 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13033) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13033 : ℕ))
    (by norm_num : (13033 : ℕ) ≤ 16384)
  have ht : paperTail256 13033 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13033 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13033 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13033 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13033 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13033 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13031 128 * √(2 / (13033 : ℝ)) *
      (√(13033 : ℝ) + paperT0 13033 + paperTail256 13033) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13033 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13033 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13033 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13031 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13031 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13033 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13033

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13033
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13033 (61 / 100) 165 (17 / (100 * 13033)) (26 / (10 * 13033)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13033 (61 / 100) 165 (17 / (100 * 13033)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (440943843 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1353314967 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4155871459 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13033 / 13033 * (61 / 100)) ^ 4 * inverseRadius8 (13033 - 1) /
            envelopeGap 13033 (61 / 100) 165 (17 / (100 * 13033)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13033

namespace BstLean.Part266.Row13033
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13033 165 ≤ (21477727 / 5000000000000000)
  f1 : (tableEnvelope C).f1 13033 165 ≤ (35826663 / 25000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (43054757 / 125000000000000000)
  w0 : (tableEnvelope C).w0 13033 165 ≤ (21202933 / 1250000000000000000)
  w1 : (tableEnvelope C).w1 13033 165 ≤ (37713703 / 3125000000000000000)
  w2 : (tableEnvelope C).w2 13033 165 ≤ (440947869 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (440943843 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (440943843 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1353314967 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4155871459 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3611621 / 1000000000) : ℝ) ≤ √(17 / (100 * 13033) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13033) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2099866289 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3678742947 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13033) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13033) ≤ (10851021 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13033) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13033 * (165 : ℝ) ^ 2 + 26 / (10 * 13033) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13033) : ℝ)) (tA 13033 * 165 ^ 2 + 26 / (10 * 13033)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3611621 / 1000000000))) * ((440943843 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3611621 / 1000000000)) ^ 3) * ((1353314967 / 1000000000000000000000000))) + ((4155871459 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3611621 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13033) : ℝ)) d.D d.V d.P (√(tA 13033) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3611621 / 1000000000)) ^ 2 * (((2099866289 / 1000000000000000)) * ((3678742947 / 100000000000000000)))) + ((4155871459 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13033) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3611621 / 1000000000)) * ((440943843 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13033) : ℝ)) (tA 13033 * 165 ^ 2 + 26 / (10 * 13033)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((440943843 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3611621 / 1000000000)) ^ 2) * ((1353314967 / 1000000000000000000000000)) + ((4155871459 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13033) : ℝ)) (√(26 / (10 * 13033) : ℝ)) d.D d.V d.P (√(tA 13033) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3611621 / 1000000000)) * (((2099866289 / 1000000000000000)) * ((3678742947 / 100000000000000000))) + ((4155871459 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13033) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((440943843 / 100000000000000000000) : ℝ) + ((4155871459 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13033

namespace BstLean.Part266.Row13033
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13033 165 ∧
    0 ≤ (tableEnvelope C).f1 13033 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13033 165 ∧
    0 ≤ (tableEnvelope C).w1 13033 165 ∧ 0 ≤ (tableEnvelope C).w2 13033 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13033 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13033 165 ∧ 0 ≤ d.f1 13033 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13033 165 ∧ 0 ≤ d.w1 13033 165 ∧ 0 ≤ d.w2 13033 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13033 ≤ 2 * (228 / 100 : ℝ) / 13033 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13033 ≤ 2 * (370 / 100 : ℝ) / 13033 := by
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
    (completeRAData (tableEnvelope C) 13033 165).locationBound 13033 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13033 165).energyBound 13033 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13033 165) (d.f1 13033 165) d.f2 ≤
      32 * (((21477727 / 5000000000000000) : ℝ) + (35826663 / 25000000000000000) + (43054757 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13033 165) (d.w1 13033 165)
      (d.w2 13033 165) ≤
      32 * (((21202933 / 1250000000000000000) : ℝ) + (37713703 / 3125000000000000000) + (440947869 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13033 165) (d.f1 13033 165) d.f2 ≤
      ((21477727 / 5000000000000000) : ℝ) ^ 2 + 2 * ((21477727 / 5000000000000000)) * ((35826663 / 25000000000000000)) * (126 / 100) +
      2 * (((35826663 / 25000000000000000)) ^ 2 + 2 * ((21477727 / 5000000000000000)) * ((43054757 / 125000000000000000))) +
      6 * ((35826663 / 25000000000000000)) * ((43054757 / 125000000000000000)) * (126 / 100) + 8 * ((43054757 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13033 165) (d.f1 13033 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13033 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13033 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13033 165) (d.f1 13033 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13033 165) (d.w1 13033 165) (d.w2 13033 165)
  have hwexpr0 : 0 ≤ d.w0 13033 165 + d.w1 13033 165 * √(π / 2) +
      2 * d.w2 13033 165 + energyR16 13033 *
      radiusPolynomialRoot16 (d.w0 13033 165) (d.w1 13033 165) (d.w2 13033 165) := by
    positivity
  constructor
  · change (13033 : ℝ) ^ 8 * (mA 13033 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13033 165) (d.f1 13033 165) d.f2 + locationR16 13033 *
        radiusPolynomialRoot16 (d.f0 13033 165) (d.f1 13033 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13033 : ℝ) ^ 8 * (mA 13033 : ℝ) ^ 8 *
        ((((21477727 / 5000000000000000) : ℝ) ^ 2 + 2 * ((21477727 / 5000000000000000)) * ((35826663 / 25000000000000000)) * (126 / 100) +
          2 * (((35826663 / 25000000000000000)) ^ 2 + 2 * ((21477727 / 5000000000000000)) * ((43054757 / 125000000000000000))) +
          6 * ((35826663 / 25000000000000000)) * ((43054757 / 125000000000000000)) * (126 / 100) + 8 * ((43054757 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13033) *
          (32 * (((21477727 / 5000000000000000) : ℝ) + (35826663 / 25000000000000000) + (43054757 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13033 : ℝ) ^ 16 *
      (d.w0 13033 165 + d.w1 13033 165 * √(π / 2) + 2 * d.w2 13033 165 +
        energyR16 13033 * radiusPolynomialRoot16 (d.w0 13033 165) (d.w1 13033 165)
          (d.w2 13033 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13033 : ℝ) ^ 16 *
        (((21202933 / 1250000000000000000) : ℝ) + ((37713703 / 3125000000000000000)) * (126 / 100) + 2 * ((440947869 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13033) *
          (32 * (((21202933 / 1250000000000000000) : ℝ) + (37713703 / 3125000000000000000) + (440947869 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13033

/-! A coarse bound on the actual paper statistics constant at dimension 13034. -/
namespace BstLean.Part266.Row13034
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13032 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13032 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13032 128 ≤ (13286 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13286 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13034) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13034 : ℕ))
    (by norm_num : (13034 : ℕ) ≤ 16384)
  have ht : paperTail256 13034 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13034 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13034 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13034 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13034 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13034 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13032 128 * √(2 / (13034 : ℝ)) *
      (√(13034 : ℝ) + paperT0 13034 + paperTail256 13034) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13034 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13034 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13034 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13032 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13032 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13034 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13034

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13034
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13034 (61 / 100) 165 (17 / (100 * 13034)) (26 / (10 * 13034)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13034 (61 / 100) 165 (17 / (100 * 13034)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (88168471 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (8455623 / 6250000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2076648599 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13034 / 13034 * (61 / 100)) ^ 4 * inverseRadius8 (13034 - 1) /
            envelopeGap 13034 (61 / 100) 165 (17 / (100 * 13034)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13034

namespace BstLean.Part266.Row13034
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13034 165 ≤ (10736799 / 2500000000000000)
  f1 : (tableEnvelope C).f1 13034 165 ≤ (1432791213 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (172185969 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13034 165 ≤ (33916877 / 2000000000000000000)
  w1 : (tableEnvelope C).w1 13034 165 ≤ (603280273 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13034 165 ≤ (440846379 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (88168471 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (88168471 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (8455623 / 6250000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2076648599 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3611483 / 1000000000) : ℝ) ≤ √(17 / (100 * 13034) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13034) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1049812311 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36781784623 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13034) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13034) ≤ (21700377 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13034) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13034 * (165 : ℝ) ^ 2 + 26 / (10 * 13034) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13034) : ℝ)) (tA 13034 * 165 ^ 2 + 26 / (10 * 13034)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3611483 / 1000000000))) * ((88168471 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3611483 / 1000000000)) ^ 3) * ((8455623 / 6250000000000000000000))) + ((2076648599 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3611483 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13034) : ℝ)) d.D d.V d.P (√(tA 13034) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3611483 / 1000000000)) ^ 2 * (((1049812311 / 500000000000000)) * ((36781784623 / 1000000000000000000)))) + ((2076648599 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13034) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3611483 / 1000000000)) * ((88168471 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13034) : ℝ)) (tA 13034 * 165 ^ 2 + 26 / (10 * 13034)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((88168471 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3611483 / 1000000000)) ^ 2) * ((8455623 / 6250000000000000000000)) + ((2076648599 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13034) : ℝ)) (√(26 / (10 * 13034) : ℝ)) d.D d.V d.P (√(tA 13034) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3611483 / 1000000000)) * (((1049812311 / 500000000000000)) * ((36781784623 / 1000000000000000000))) + ((2076648599 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13034) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((88168471 / 20000000000000000000) : ℝ) + ((2076648599 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13034

namespace BstLean.Part266.Row13034
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13034 165 ∧
    0 ≤ (tableEnvelope C).f1 13034 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13034 165 ∧
    0 ≤ (tableEnvelope C).w1 13034 165 ∧ 0 ≤ (tableEnvelope C).w2 13034 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13034 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13034 165 ∧ 0 ≤ d.f1 13034 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13034 165 ∧ 0 ≤ d.w1 13034 165 ∧ 0 ≤ d.w2 13034 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13034 ≤ 2 * (228 / 100 : ℝ) / 13034 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13034 ≤ 2 * (370 / 100 : ℝ) / 13034 := by
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
    (completeRAData (tableEnvelope C) 13034 165).locationBound 13034 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13034 165).energyBound 13034 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13034 165) (d.f1 13034 165) d.f2 ≤
      32 * (((10736799 / 2500000000000000) : ℝ) + (1432791213 / 1000000000000000000) + (172185969 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13034 165) (d.w1 13034 165)
      (d.w2 13034 165) ≤
      32 * (((33916877 / 2000000000000000000) : ℝ) + (603280273 / 50000000000000000000) + (440846379 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13034 165) (d.f1 13034 165) d.f2 ≤
      ((10736799 / 2500000000000000) : ℝ) ^ 2 + 2 * ((10736799 / 2500000000000000)) * ((1432791213 / 1000000000000000000)) * (126 / 100) +
      2 * (((1432791213 / 1000000000000000000)) ^ 2 + 2 * ((10736799 / 2500000000000000)) * ((172185969 / 500000000000000000))) +
      6 * ((1432791213 / 1000000000000000000)) * ((172185969 / 500000000000000000)) * (126 / 100) + 8 * ((172185969 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13034 165) (d.f1 13034 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13034 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13034 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13034 165) (d.f1 13034 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13034 165) (d.w1 13034 165) (d.w2 13034 165)
  have hwexpr0 : 0 ≤ d.w0 13034 165 + d.w1 13034 165 * √(π / 2) +
      2 * d.w2 13034 165 + energyR16 13034 *
      radiusPolynomialRoot16 (d.w0 13034 165) (d.w1 13034 165) (d.w2 13034 165) := by
    positivity
  constructor
  · change (13034 : ℝ) ^ 8 * (mA 13034 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13034 165) (d.f1 13034 165) d.f2 + locationR16 13034 *
        radiusPolynomialRoot16 (d.f0 13034 165) (d.f1 13034 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13034 : ℝ) ^ 8 * (mA 13034 : ℝ) ^ 8 *
        ((((10736799 / 2500000000000000) : ℝ) ^ 2 + 2 * ((10736799 / 2500000000000000)) * ((1432791213 / 1000000000000000000)) * (126 / 100) +
          2 * (((1432791213 / 1000000000000000000)) ^ 2 + 2 * ((10736799 / 2500000000000000)) * ((172185969 / 500000000000000000))) +
          6 * ((1432791213 / 1000000000000000000)) * ((172185969 / 500000000000000000)) * (126 / 100) + 8 * ((172185969 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13034) *
          (32 * (((10736799 / 2500000000000000) : ℝ) + (1432791213 / 1000000000000000000) + (172185969 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13034 : ℝ) ^ 16 *
      (d.w0 13034 165 + d.w1 13034 165 * √(π / 2) + 2 * d.w2 13034 165 +
        energyR16 13034 * radiusPolynomialRoot16 (d.w0 13034 165) (d.w1 13034 165)
          (d.w2 13034 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13034 : ℝ) ^ 16 *
        (((33916877 / 2000000000000000000) : ℝ) + ((603280273 / 50000000000000000000)) * (126 / 100) + 2 * ((440846379 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13034) *
          (32 * (((33916877 / 2000000000000000000) : ℝ) + (603280273 / 50000000000000000000) + (440846379 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13034

/-! A coarse bound on the actual paper statistics constant at dimension 13035. -/
namespace BstLean.Part266.Row13035
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13033 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13033 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13033 128 ≤ (13287 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13287 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13035) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13035 : ℕ))
    (by norm_num : (13035 : ℕ) ≤ 16384)
  have ht : paperTail256 13035 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13035 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13035 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13035 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13035 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13035 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13033 128 * √(2 / (13035 : ℝ)) *
      (√(13035 : ℝ) + paperT0 13035 + paperTail256 13035) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13035 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13035 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13035 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13033 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13033 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13035 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13035

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13035
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13035 (61 / 100) 165 (17 / (100 * 13035)) (26 / (10 * 13035)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13035 (61 / 100) 165 (17 / (100 * 13035)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (220370449 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1352484553 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1037681183 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13035 / 13035 * (61 / 100)) ^ 4 * inverseRadius8 (13035 - 1) /
            envelopeGap 13035 (61 / 100) 165 (17 / (100 * 13035)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13035

namespace BstLean.Part266.Row13035
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13035 165 ≤ (429389751 / 100000000000000000)
  f1 : (tableEnvelope C).f1 13035 165 ≤ (286503357 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (68861187 / 200000000000000000)
  w0 : (tableEnvelope C).w0 13035 165 ≤ (1695453887 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13035 165 ≤ (1206283019 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13035 165 ≤ (440744919 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (220370449 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (220370449 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1352484553 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1037681183 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((225709 / 62500000) : ℝ) ≤ √(17 / (100 * 13035) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13035) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2099383 / 1000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9194035271 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13035) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13035) ≤ (108493561 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13035) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13035 * (165 : ℝ) ^ 2 + 26 / (10 * 13035) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13035) : ℝ)) (tA 13035 * 165 ^ 2 + 26 / (10 * 13035)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((225709 / 62500000))) * ((220370449 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((225709 / 62500000)) ^ 3) * ((1352484553 / 1000000000000000000000000))) + ((1037681183 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((225709 / 62500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13035) : ℝ)) d.D d.V d.P (√(tA 13035) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((225709 / 62500000)) ^ 2 * (((2099383 / 1000000000000)) * ((9194035271 / 250000000000000000)))) + ((1037681183 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13035) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((225709 / 62500000)) * ((220370449 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13035) : ℝ)) (tA 13035 * 165 ^ 2 + 26 / (10 * 13035)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((220370449 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((225709 / 62500000)) ^ 2) * ((1352484553 / 1000000000000000000000000)) + ((1037681183 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13035) : ℝ)) (√(26 / (10 * 13035) : ℝ)) d.D d.V d.P (√(tA 13035) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((225709 / 62500000)) * (((2099383 / 1000000000000)) * ((9194035271 / 250000000000000000))) + ((1037681183 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13035) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((220370449 / 50000000000000000000) : ℝ) + ((1037681183 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13035

namespace BstLean.Part266.Row13035
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13035 165 ∧
    0 ≤ (tableEnvelope C).f1 13035 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13035 165 ∧
    0 ≤ (tableEnvelope C).w1 13035 165 ∧ 0 ≤ (tableEnvelope C).w2 13035 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13035 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13035 165 ∧ 0 ≤ d.f1 13035 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13035 165 ∧ 0 ≤ d.w1 13035 165 ∧ 0 ≤ d.w2 13035 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13035 ≤ 2 * (228 / 100 : ℝ) / 13035 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13035 ≤ 2 * (370 / 100 : ℝ) / 13035 := by
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
    (completeRAData (tableEnvelope C) 13035 165).locationBound 13035 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13035 165).energyBound 13035 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13035 165) (d.f1 13035 165) d.f2 ≤
      32 * (((429389751 / 100000000000000000) : ℝ) + (286503357 / 200000000000000000) + (68861187 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13035 165) (d.w1 13035 165)
      (d.w2 13035 165) ≤
      32 * (((1695453887 / 100000000000000000000) : ℝ) + (1206283019 / 100000000000000000000) + (440744919 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13035 165) (d.f1 13035 165) d.f2 ≤
      ((429389751 / 100000000000000000) : ℝ) ^ 2 + 2 * ((429389751 / 100000000000000000)) * ((286503357 / 200000000000000000)) * (126 / 100) +
      2 * (((286503357 / 200000000000000000)) ^ 2 + 2 * ((429389751 / 100000000000000000)) * ((68861187 / 200000000000000000))) +
      6 * ((286503357 / 200000000000000000)) * ((68861187 / 200000000000000000)) * (126 / 100) + 8 * ((68861187 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13035 165) (d.f1 13035 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13035 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13035 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13035 165) (d.f1 13035 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13035 165) (d.w1 13035 165) (d.w2 13035 165)
  have hwexpr0 : 0 ≤ d.w0 13035 165 + d.w1 13035 165 * √(π / 2) +
      2 * d.w2 13035 165 + energyR16 13035 *
      radiusPolynomialRoot16 (d.w0 13035 165) (d.w1 13035 165) (d.w2 13035 165) := by
    positivity
  constructor
  · change (13035 : ℝ) ^ 8 * (mA 13035 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13035 165) (d.f1 13035 165) d.f2 + locationR16 13035 *
        radiusPolynomialRoot16 (d.f0 13035 165) (d.f1 13035 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13035 : ℝ) ^ 8 * (mA 13035 : ℝ) ^ 8 *
        ((((429389751 / 100000000000000000) : ℝ) ^ 2 + 2 * ((429389751 / 100000000000000000)) * ((286503357 / 200000000000000000)) * (126 / 100) +
          2 * (((286503357 / 200000000000000000)) ^ 2 + 2 * ((429389751 / 100000000000000000)) * ((68861187 / 200000000000000000))) +
          6 * ((286503357 / 200000000000000000)) * ((68861187 / 200000000000000000)) * (126 / 100) + 8 * ((68861187 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13035) *
          (32 * (((429389751 / 100000000000000000) : ℝ) + (286503357 / 200000000000000000) + (68861187 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13035 : ℝ) ^ 16 *
      (d.w0 13035 165 + d.w1 13035 165 * √(π / 2) + 2 * d.w2 13035 165 +
        energyR16 13035 * radiusPolynomialRoot16 (d.w0 13035 165) (d.w1 13035 165)
          (d.w2 13035 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13035 : ℝ) ^ 16 *
        (((1695453887 / 100000000000000000000) : ℝ) + ((1206283019 / 100000000000000000000)) * (126 / 100) + 2 * ((440744919 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13035) *
          (32 * (((1695453887 / 100000000000000000000) : ℝ) + (1206283019 / 100000000000000000000) + (440744919 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13035

/-! A coarse bound on the actual paper statistics constant at dimension 13036. -/
namespace BstLean.Part266.Row13036
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13034 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13034 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13034 128 ≤ (13288 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13288 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13036) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13036 : ℕ))
    (by norm_num : (13036 : ℕ) ≤ 16384)
  have ht : paperTail256 13036 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13036 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13036 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13036 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13036 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13036 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13034 128 * √(2 / (13036 : ℝ)) *
      (√(13036 : ℝ) + paperT0 13036 + paperTail256 13036) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13036 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13036 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13036 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13034 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13034 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13036 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13036

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13036
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13036 (61 / 100) 165 (17 / (100 * 13036)) (26 / (10 * 13036)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13036 (61 / 100) 165 (17 / (100 * 13036)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (27539967 / 6250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (270413917 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4148154061 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13036 / 13036 * (61 / 100)) ^ 4 * inverseRadius8 (13036 - 1) /
            envelopeGap 13036 (61 / 100) 165 (17 / (100 * 13036)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13036

namespace BstLean.Part266.Row13036
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13036 165 ≤ (536634033 / 125000000000000000)
  f1 : (tableEnvelope C).f1 13036 165 ≤ (1432241651 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (68847971 / 200000000000000000)
  w0 : (tableEnvelope C).w0 13036 165 ≤ (1695063359 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13036 165 ≤ (1206005249 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13036 165 ≤ (440643491 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (27539967 / 6250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (27539967 / 6250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (270413917 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4148154061 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1805603 / 500000000) : ℝ) ≤ √(17 / (100 * 13036) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13036) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (83965657 / 40000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36770498841 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13036) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13036) ≤ (54242619 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13036) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13036 * (165 : ℝ) ^ 2 + 26 / (10 * 13036) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13036) : ℝ)) (tA 13036 * 165 ^ 2 + 26 / (10 * 13036)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1805603 / 500000000))) * ((27539967 / 6250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1805603 / 500000000)) ^ 3) * ((270413917 / 200000000000000000000000))) + ((4148154061 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1805603 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13036) : ℝ)) d.D d.V d.P (√(tA 13036) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1805603 / 500000000)) ^ 2 * (((83965657 / 40000000000000)) * ((36770498841 / 1000000000000000000)))) + ((4148154061 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13036) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1805603 / 500000000)) * ((27539967 / 6250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13036) : ℝ)) (tA 13036 * 165 ^ 2 + 26 / (10 * 13036)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((27539967 / 6250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1805603 / 500000000)) ^ 2) * ((270413917 / 200000000000000000000000)) + ((4148154061 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13036) : ℝ)) (√(26 / (10 * 13036) : ℝ)) d.D d.V d.P (√(tA 13036) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1805603 / 500000000)) * (((83965657 / 40000000000000)) * ((36770498841 / 1000000000000000000))) + ((4148154061 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13036) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((27539967 / 6250000000000000000) : ℝ) + ((4148154061 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13036

namespace BstLean.Part266.Row13036
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13036 165 ∧
    0 ≤ (tableEnvelope C).f1 13036 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13036 165 ∧
    0 ≤ (tableEnvelope C).w1 13036 165 ∧ 0 ≤ (tableEnvelope C).w2 13036 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13036 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13036 165 ∧ 0 ≤ d.f1 13036 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13036 165 ∧ 0 ≤ d.w1 13036 165 ∧ 0 ≤ d.w2 13036 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13036 ≤ 2 * (228 / 100 : ℝ) / 13036 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13036 ≤ 2 * (370 / 100 : ℝ) / 13036 := by
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
    (completeRAData (tableEnvelope C) 13036 165).locationBound 13036 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13036 165).energyBound 13036 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13036 165) (d.f1 13036 165) d.f2 ≤
      32 * (((536634033 / 125000000000000000) : ℝ) + (1432241651 / 1000000000000000000) + (68847971 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13036 165) (d.w1 13036 165)
      (d.w2 13036 165) ≤
      32 * (((1695063359 / 100000000000000000000) : ℝ) + (1206005249 / 100000000000000000000) + (440643491 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13036 165) (d.f1 13036 165) d.f2 ≤
      ((536634033 / 125000000000000000) : ℝ) ^ 2 + 2 * ((536634033 / 125000000000000000)) * ((1432241651 / 1000000000000000000)) * (126 / 100) +
      2 * (((1432241651 / 1000000000000000000)) ^ 2 + 2 * ((536634033 / 125000000000000000)) * ((68847971 / 200000000000000000))) +
      6 * ((1432241651 / 1000000000000000000)) * ((68847971 / 200000000000000000)) * (126 / 100) + 8 * ((68847971 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13036 165) (d.f1 13036 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13036 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13036 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13036 165) (d.f1 13036 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13036 165) (d.w1 13036 165) (d.w2 13036 165)
  have hwexpr0 : 0 ≤ d.w0 13036 165 + d.w1 13036 165 * √(π / 2) +
      2 * d.w2 13036 165 + energyR16 13036 *
      radiusPolynomialRoot16 (d.w0 13036 165) (d.w1 13036 165) (d.w2 13036 165) := by
    positivity
  constructor
  · change (13036 : ℝ) ^ 8 * (mA 13036 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13036 165) (d.f1 13036 165) d.f2 + locationR16 13036 *
        radiusPolynomialRoot16 (d.f0 13036 165) (d.f1 13036 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13036 : ℝ) ^ 8 * (mA 13036 : ℝ) ^ 8 *
        ((((536634033 / 125000000000000000) : ℝ) ^ 2 + 2 * ((536634033 / 125000000000000000)) * ((1432241651 / 1000000000000000000)) * (126 / 100) +
          2 * (((1432241651 / 1000000000000000000)) ^ 2 + 2 * ((536634033 / 125000000000000000)) * ((68847971 / 200000000000000000))) +
          6 * ((1432241651 / 1000000000000000000)) * ((68847971 / 200000000000000000)) * (126 / 100) + 8 * ((68847971 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13036) *
          (32 * (((536634033 / 125000000000000000) : ℝ) + (1432241651 / 1000000000000000000) + (68847971 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13036 : ℝ) ^ 16 *
      (d.w0 13036 165 + d.w1 13036 165 * √(π / 2) + 2 * d.w2 13036 165 +
        energyR16 13036 * radiusPolynomialRoot16 (d.w0 13036 165) (d.w1 13036 165)
          (d.w2 13036 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13036 : ℝ) ^ 16 *
        (((1695063359 / 100000000000000000000) : ℝ) + ((1206005249 / 100000000000000000000)) * (126 / 100) + 2 * ((440643491 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13036) *
          (32 * (((1695063359 / 100000000000000000000) : ℝ) + (1206005249 / 100000000000000000000) + (440643491 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13036

/-! A coarse bound on the actual paper statistics constant at dimension 13037. -/
namespace BstLean.Part266.Row13037
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13035 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13035 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13035 128 ≤ (13289 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13289 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13037) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13037 : ℕ))
    (by norm_num : (13037 : ℕ) ≤ 16384)
  have ht : paperTail256 13037 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13037 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13037 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13037 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13037 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13037 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13035 128 * √(2 / (13037 : ℝ)) *
      (√(13037 : ℝ) + paperT0 13037 + paperTail256 13037) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13037 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13037 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13037 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13035 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13035 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13037 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13037

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13037
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13037 (61 / 100) 165 (17 / (100 * 13037)) (26 / (10 * 13037)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13037 (61 / 100) 165 (17 / (100 * 13037)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (440538077 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (168956847 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2072792591 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13037 / 13037 * (61 / 100)) ^ 4 * inverseRadius8 (13037 - 1) /
            envelopeGap 13037 (61 / 100) 165 (17 / (100 * 13037)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13037

namespace BstLean.Part266.Row13037
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13037 165 ≤ (171690029 / 40000000000000000)
  f1 : (tableEnvelope C).f1 13037 165 ≤ (357991849 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (34417389 / 100000000000000000)
  w0 : (tableEnvelope C).w0 13037 165 ≤ (1694673657 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13037 165 ≤ (1205727903 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13037 165 ≤ (440542093 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (440538077 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (440538077 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (168956847 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2072792591 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3611067 / 1000000000) : ℝ) ≤ √(17 / (100 * 13037) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13037) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (262362487 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7352971579 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13037) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13037) ≤ (108476917 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13037) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13037 * (165 : ℝ) ^ 2 + 26 / (10 * 13037) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13037) : ℝ)) (tA 13037 * 165 ^ 2 + 26 / (10 * 13037)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3611067 / 1000000000))) * ((440538077 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3611067 / 1000000000)) ^ 3) * ((168956847 / 125000000000000000000000))) + ((2072792591 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3611067 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13037) : ℝ)) d.D d.V d.P (√(tA 13037) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3611067 / 1000000000)) ^ 2 * (((262362487 / 125000000000000)) * ((7352971579 / 200000000000000000)))) + ((2072792591 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13037) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3611067 / 1000000000)) * ((440538077 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13037) : ℝ)) (tA 13037 * 165 ^ 2 + 26 / (10 * 13037)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((440538077 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3611067 / 1000000000)) ^ 2) * ((168956847 / 125000000000000000000000)) + ((2072792591 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13037) : ℝ)) (√(26 / (10 * 13037) : ℝ)) d.D d.V d.P (√(tA 13037) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3611067 / 1000000000)) * (((262362487 / 125000000000000)) * ((7352971579 / 200000000000000000))) + ((2072792591 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13037) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((440538077 / 100000000000000000000) : ℝ) + ((2072792591 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13037

namespace BstLean.Part266.Row13037
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13037 165 ∧
    0 ≤ (tableEnvelope C).f1 13037 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13037 165 ∧
    0 ≤ (tableEnvelope C).w1 13037 165 ∧ 0 ≤ (tableEnvelope C).w2 13037 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13037 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13037 165 ∧ 0 ≤ d.f1 13037 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13037 165 ∧ 0 ≤ d.w1 13037 165 ∧ 0 ≤ d.w2 13037 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13037 ≤ 2 * (228 / 100 : ℝ) / 13037 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13037 ≤ 2 * (370 / 100 : ℝ) / 13037 := by
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
    (completeRAData (tableEnvelope C) 13037 165).locationBound 13037 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13037 165).energyBound 13037 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13037 165) (d.f1 13037 165) d.f2 ≤
      32 * (((171690029 / 40000000000000000) : ℝ) + (357991849 / 250000000000000000) + (34417389 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13037 165) (d.w1 13037 165)
      (d.w2 13037 165) ≤
      32 * (((1694673657 / 100000000000000000000) : ℝ) + (1205727903 / 100000000000000000000) + (440542093 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13037 165) (d.f1 13037 165) d.f2 ≤
      ((171690029 / 40000000000000000) : ℝ) ^ 2 + 2 * ((171690029 / 40000000000000000)) * ((357991849 / 250000000000000000)) * (126 / 100) +
      2 * (((357991849 / 250000000000000000)) ^ 2 + 2 * ((171690029 / 40000000000000000)) * ((34417389 / 100000000000000000))) +
      6 * ((357991849 / 250000000000000000)) * ((34417389 / 100000000000000000)) * (126 / 100) + 8 * ((34417389 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13037 165) (d.f1 13037 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13037 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13037 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13037 165) (d.f1 13037 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13037 165) (d.w1 13037 165) (d.w2 13037 165)
  have hwexpr0 : 0 ≤ d.w0 13037 165 + d.w1 13037 165 * √(π / 2) +
      2 * d.w2 13037 165 + energyR16 13037 *
      radiusPolynomialRoot16 (d.w0 13037 165) (d.w1 13037 165) (d.w2 13037 165) := by
    positivity
  constructor
  · change (13037 : ℝ) ^ 8 * (mA 13037 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13037 165) (d.f1 13037 165) d.f2 + locationR16 13037 *
        radiusPolynomialRoot16 (d.f0 13037 165) (d.f1 13037 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13037 : ℝ) ^ 8 * (mA 13037 : ℝ) ^ 8 *
        ((((171690029 / 40000000000000000) : ℝ) ^ 2 + 2 * ((171690029 / 40000000000000000)) * ((357991849 / 250000000000000000)) * (126 / 100) +
          2 * (((357991849 / 250000000000000000)) ^ 2 + 2 * ((171690029 / 40000000000000000)) * ((34417389 / 100000000000000000))) +
          6 * ((357991849 / 250000000000000000)) * ((34417389 / 100000000000000000)) * (126 / 100) + 8 * ((34417389 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13037) *
          (32 * (((171690029 / 40000000000000000) : ℝ) + (357991849 / 250000000000000000) + (34417389 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13037 : ℝ) ^ 16 *
      (d.w0 13037 165 + d.w1 13037 165 * √(π / 2) + 2 * d.w2 13037 165 +
        energyR16 13037 * radiusPolynomialRoot16 (d.w0 13037 165) (d.w1 13037 165)
          (d.w2 13037 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13037 : ℝ) ^ 16 *
        (((1694673657 / 100000000000000000000) : ℝ) + ((1205727903 / 100000000000000000000)) * (126 / 100) + 2 * ((440542093 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13037) *
          (32 * (((1694673657 / 100000000000000000000) : ℝ) + (1205727903 / 100000000000000000000) + (440542093 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13037

/-! A coarse bound on the actual paper statistics constant at dimension 13038. -/
namespace BstLean.Part266.Row13038
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13036 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13036 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13036 128 ≤ (13290 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13290 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13038) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13038 : ℕ))
    (by norm_num : (13038 : ℕ) ≤ 16384)
  have ht : paperTail256 13038 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13038 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13038 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13038 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13038 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13038 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13036 128 * √(2 / (13038 : ℝ)) *
      (√(13038 : ℝ) + paperT0 13038 + paperTail256 13038) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13038 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13038 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13038 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13036 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13036 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13038 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13038

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13038
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13038 (61 / 100) 165 (17 / (100 * 13038)) (26 / (10 * 13038)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13038 (61 / 100) 165 (17 / (100 * 13038)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (440436713 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (675620063 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (828603619 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13038 / 13038 * (61 / 100)) ^ 4 * inverseRadius8 (13038 - 1) /
            envelopeGap 13038 (61 / 100) 165 (17 / (100 * 13038)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13038

namespace BstLean.Part266.Row13038
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13038 165 ≤ (429142603 / 100000000000000000)
  f1 : (tableEnvelope C).f1 13038 165 ≤ (1431692433 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (344107849 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13038 165 ≤ (169428339 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 13038 165 ≤ (1205450313 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13038 165 ≤ (440440727 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (440436713 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (440436713 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (675620063 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (828603619 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3610929 / 1000000000) : ℝ) ≤ √(17 / (100 * 13038) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13038) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (524664603 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18379609123 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13038) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13038) ≤ (108468597 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13038) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13038 * (165 : ℝ) ^ 2 + 26 / (10 * 13038) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13038) : ℝ)) (tA 13038 * 165 ^ 2 + 26 / (10 * 13038)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3610929 / 1000000000))) * ((440436713 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3610929 / 1000000000)) ^ 3) * ((675620063 / 500000000000000000000000))) + ((828603619 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3610929 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13038) : ℝ)) d.D d.V d.P (√(tA 13038) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3610929 / 1000000000)) ^ 2 * (((524664603 / 250000000000000)) * ((18379609123 / 500000000000000000)))) + ((828603619 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13038) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3610929 / 1000000000)) * ((440436713 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13038) : ℝ)) (tA 13038 * 165 ^ 2 + 26 / (10 * 13038)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((440436713 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3610929 / 1000000000)) ^ 2) * ((675620063 / 500000000000000000000000)) + ((828603619 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13038) : ℝ)) (√(26 / (10 * 13038) : ℝ)) d.D d.V d.P (√(tA 13038) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3610929 / 1000000000)) * (((524664603 / 250000000000000)) * ((18379609123 / 500000000000000000))) + ((828603619 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13038) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((440436713 / 100000000000000000000) : ℝ) + ((828603619 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13038

namespace BstLean.Part266.Row13038
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13038 165 ∧
    0 ≤ (tableEnvelope C).f1 13038 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13038 165 ∧
    0 ≤ (tableEnvelope C).w1 13038 165 ∧ 0 ≤ (tableEnvelope C).w2 13038 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13038 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13038 165 ∧ 0 ≤ d.f1 13038 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13038 165 ∧ 0 ≤ d.w1 13038 165 ∧ 0 ≤ d.w2 13038 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13038 ≤ 2 * (228 / 100 : ℝ) / 13038 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13038 ≤ 2 * (370 / 100 : ℝ) / 13038 := by
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
    (completeRAData (tableEnvelope C) 13038 165).locationBound 13038 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13038 165).energyBound 13038 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13038 165) (d.f1 13038 165) d.f2 ≤
      32 * (((429142603 / 100000000000000000) : ℝ) + (1431692433 / 1000000000000000000) + (344107849 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13038 165) (d.w1 13038 165)
      (d.w2 13038 165) ≤
      32 * (((169428339 / 10000000000000000000) : ℝ) + (1205450313 / 100000000000000000000) + (440440727 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13038 165) (d.f1 13038 165) d.f2 ≤
      ((429142603 / 100000000000000000) : ℝ) ^ 2 + 2 * ((429142603 / 100000000000000000)) * ((1431692433 / 1000000000000000000)) * (126 / 100) +
      2 * (((1431692433 / 1000000000000000000)) ^ 2 + 2 * ((429142603 / 100000000000000000)) * ((344107849 / 1000000000000000000))) +
      6 * ((1431692433 / 1000000000000000000)) * ((344107849 / 1000000000000000000)) * (126 / 100) + 8 * ((344107849 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13038 165) (d.f1 13038 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13038 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13038 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13038 165) (d.f1 13038 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13038 165) (d.w1 13038 165) (d.w2 13038 165)
  have hwexpr0 : 0 ≤ d.w0 13038 165 + d.w1 13038 165 * √(π / 2) +
      2 * d.w2 13038 165 + energyR16 13038 *
      radiusPolynomialRoot16 (d.w0 13038 165) (d.w1 13038 165) (d.w2 13038 165) := by
    positivity
  constructor
  · change (13038 : ℝ) ^ 8 * (mA 13038 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13038 165) (d.f1 13038 165) d.f2 + locationR16 13038 *
        radiusPolynomialRoot16 (d.f0 13038 165) (d.f1 13038 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13038 : ℝ) ^ 8 * (mA 13038 : ℝ) ^ 8 *
        ((((429142603 / 100000000000000000) : ℝ) ^ 2 + 2 * ((429142603 / 100000000000000000)) * ((1431692433 / 1000000000000000000)) * (126 / 100) +
          2 * (((1431692433 / 1000000000000000000)) ^ 2 + 2 * ((429142603 / 100000000000000000)) * ((344107849 / 1000000000000000000))) +
          6 * ((1431692433 / 1000000000000000000)) * ((344107849 / 1000000000000000000)) * (126 / 100) + 8 * ((344107849 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13038) *
          (32 * (((429142603 / 100000000000000000) : ℝ) + (1431692433 / 1000000000000000000) + (344107849 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13038 : ℝ) ^ 16 *
      (d.w0 13038 165 + d.w1 13038 165 * √(π / 2) + 2 * d.w2 13038 165 +
        energyR16 13038 * radiusPolynomialRoot16 (d.w0 13038 165) (d.w1 13038 165)
          (d.w2 13038 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13038 : ℝ) ^ 16 *
        (((169428339 / 10000000000000000000) : ℝ) + ((1205450313 / 100000000000000000000)) * (126 / 100) + 2 * ((440440727 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13038) *
          (32 * (((169428339 / 10000000000000000000) : ℝ) + (1205450313 / 100000000000000000000) + (440440727 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13038

/-! A coarse bound on the actual paper statistics constant at dimension 13039. -/
namespace BstLean.Part266.Row13039
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13037 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13037 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13037 128 ≤ (13291 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13291 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13039) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13039 : ℕ))
    (by norm_num : (13039 : ℕ) ≤ 16384)
  have ht : paperTail256 13039 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13039 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13039 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13039 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13039 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13039 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13037 128 * √(2 / (13039 : ℝ)) *
      (√(13039 : ℝ) + paperT0 13039 + paperTail256 13039) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13039 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13039 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13039 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13037 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13037 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13039 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13039

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13039
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13039 (61 / 100) 165 (17 / (100 * 13039)) (26 / (10 * 13039)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13039 (61 / 100) 165 (17 / (100 * 13039)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (22016769 / 5000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (270165127 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2070226399 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13039 / 13039 * (61 / 100)) ^ 4 * inverseRadius8 (13039 - 1) /
            envelopeGap 13039 (61 / 100) 165 (17 / (100 * 13039)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13039

namespace BstLean.Part266.Row13039
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13039 165 ≤ (4290605041 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13039 165 ≤ (28628367 / 20000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (344041923 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13039 165 ≤ (1693893949 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13039 165 ≤ (301293287 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 13039 165 ≤ (440339391 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (22016769 / 5000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (22016769 / 5000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (270165127 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2070226399 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((361079 / 100000000) : ℝ) ≤ √(17 / (100 * 13039) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13039) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (83936679 / 40000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18376789947 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13039) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13039) ≤ (54230139 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13039) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13039 * (165 : ℝ) ^ 2 + 26 / (10 * 13039) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13039) : ℝ)) (tA 13039 * 165 ^ 2 + 26 / (10 * 13039)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((361079 / 100000000))) * ((22016769 / 5000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((361079 / 100000000)) ^ 3) * ((270165127 / 200000000000000000000000))) + ((2070226399 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((361079 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13039) : ℝ)) d.D d.V d.P (√(tA 13039) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((361079 / 100000000)) ^ 2 * (((83936679 / 40000000000000)) * ((18376789947 / 500000000000000000)))) + ((2070226399 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13039) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((361079 / 100000000)) * ((22016769 / 5000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13039) : ℝ)) (tA 13039 * 165 ^ 2 + 26 / (10 * 13039)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((22016769 / 5000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((361079 / 100000000)) ^ 2) * ((270165127 / 200000000000000000000000)) + ((2070226399 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13039) : ℝ)) (√(26 / (10 * 13039) : ℝ)) d.D d.V d.P (√(tA 13039) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((361079 / 100000000)) * (((83936679 / 40000000000000)) * ((18376789947 / 500000000000000000))) + ((2070226399 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13039) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((22016769 / 5000000000000000000) : ℝ) + ((2070226399 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13039

namespace BstLean.Part266.Row13039
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13039 165 ∧
    0 ≤ (tableEnvelope C).f1 13039 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13039 165 ∧
    0 ≤ (tableEnvelope C).w1 13039 165 ∧ 0 ≤ (tableEnvelope C).w2 13039 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13039 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13039 165 ∧ 0 ≤ d.f1 13039 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13039 165 ∧ 0 ≤ d.w1 13039 165 ∧ 0 ≤ d.w2 13039 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13039 ≤ 2 * (228 / 100 : ℝ) / 13039 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13039 ≤ 2 * (370 / 100 : ℝ) / 13039 := by
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
    (completeRAData (tableEnvelope C) 13039 165).locationBound 13039 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13039 165).energyBound 13039 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13039 165) (d.f1 13039 165) d.f2 ≤
      32 * (((4290605041 / 1000000000000000000) : ℝ) + (28628367 / 20000000000000000) + (344041923 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13039 165) (d.w1 13039 165)
      (d.w2 13039 165) ≤
      32 * (((1693893949 / 100000000000000000000) : ℝ) + (301293287 / 25000000000000000000) + (440339391 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13039 165) (d.f1 13039 165) d.f2 ≤
      ((4290605041 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4290605041 / 1000000000000000000)) * ((28628367 / 20000000000000000)) * (126 / 100) +
      2 * (((28628367 / 20000000000000000)) ^ 2 + 2 * ((4290605041 / 1000000000000000000)) * ((344041923 / 1000000000000000000))) +
      6 * ((28628367 / 20000000000000000)) * ((344041923 / 1000000000000000000)) * (126 / 100) + 8 * ((344041923 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13039 165) (d.f1 13039 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13039 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13039 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13039 165) (d.f1 13039 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13039 165) (d.w1 13039 165) (d.w2 13039 165)
  have hwexpr0 : 0 ≤ d.w0 13039 165 + d.w1 13039 165 * √(π / 2) +
      2 * d.w2 13039 165 + energyR16 13039 *
      radiusPolynomialRoot16 (d.w0 13039 165) (d.w1 13039 165) (d.w2 13039 165) := by
    positivity
  constructor
  · change (13039 : ℝ) ^ 8 * (mA 13039 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13039 165) (d.f1 13039 165) d.f2 + locationR16 13039 *
        radiusPolynomialRoot16 (d.f0 13039 165) (d.f1 13039 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13039 : ℝ) ^ 8 * (mA 13039 : ℝ) ^ 8 *
        ((((4290605041 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4290605041 / 1000000000000000000)) * ((28628367 / 20000000000000000)) * (126 / 100) +
          2 * (((28628367 / 20000000000000000)) ^ 2 + 2 * ((4290605041 / 1000000000000000000)) * ((344041923 / 1000000000000000000))) +
          6 * ((28628367 / 20000000000000000)) * ((344041923 / 1000000000000000000)) * (126 / 100) + 8 * ((344041923 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13039) *
          (32 * (((4290605041 / 1000000000000000000) : ℝ) + (28628367 / 20000000000000000) + (344041923 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13039 : ℝ) ^ 16 *
      (d.w0 13039 165 + d.w1 13039 165 * √(π / 2) + 2 * d.w2 13039 165 +
        energyR16 13039 * radiusPolynomialRoot16 (d.w0 13039 165) (d.w1 13039 165)
          (d.w2 13039 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13039 : ℝ) ^ 16 *
        (((1693893949 / 100000000000000000000) : ℝ) + ((301293287 / 25000000000000000000)) * (126 / 100) + 2 * ((440339391 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13039) *
          (32 * (((1693893949 / 100000000000000000000) : ℝ) + (301293287 / 25000000000000000000) + (440339391 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13039

/-! A coarse bound on the actual paper statistics constant at dimension 13040. -/
namespace BstLean.Part266.Row13040
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13038 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13038 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13038 128 ≤ (13292 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13292 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13040) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13040 : ℕ))
    (by norm_num : (13040 : ℕ) ≤ 16384)
  have ht : paperTail256 13040 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13040 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13040 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13040 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13040 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13040 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13038 128 * √(2 / (13040 : ℝ)) *
      (√(13040 : ℝ) + paperT0 13040 + paperTail256 13040) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13040 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13040 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13040 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13038 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13038 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13040 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13040

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13040
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13040 (61 / 100) 165 (17 / (100 * 13040)) (26 / (10 * 13040)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13040 (61 / 100) 165 (17 / (100 * 13040)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (440234079 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1350411303 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (413788929 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13040 / 13040 * (61 / 100)) ^ 4 * inverseRadius8 (13040 - 1) /
            envelopeGap 13040 (61 / 100) 165 (17 / (100 * 13040)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13040

namespace BstLean.Part266.Row13040
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13040 165 ≤ (2144890449 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13040 165 ≤ (1431143563 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (343975921 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13040 165 ≤ (338700789 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 13040 165 ≤ (1204895741 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13040 165 ≤ (55029761 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (440234079 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (440234079 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1350411303 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (413788929 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((902663 / 250000000) : ℝ) ≤ √(17 / (100 * 13040) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13040) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2098175587 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36747942841 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13040) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13040) ≤ (108451961 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13040) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13040 * (165 : ℝ) ^ 2 + 26 / (10 * 13040) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13040) : ℝ)) (tA 13040 * 165 ^ 2 + 26 / (10 * 13040)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((902663 / 250000000))) * ((440234079 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((902663 / 250000000)) ^ 3) * ((1350411303 / 1000000000000000000000000))) + ((413788929 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((902663 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13040) : ℝ)) d.D d.V d.P (√(tA 13040) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((902663 / 250000000)) ^ 2 * (((2098175587 / 1000000000000000)) * ((36747942841 / 1000000000000000000)))) + ((413788929 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13040) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((902663 / 250000000)) * ((440234079 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13040) : ℝ)) (tA 13040 * 165 ^ 2 + 26 / (10 * 13040)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((440234079 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((902663 / 250000000)) ^ 2) * ((1350411303 / 1000000000000000000000000)) + ((413788929 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13040) : ℝ)) (√(26 / (10 * 13040) : ℝ)) d.D d.V d.P (√(tA 13040) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((902663 / 250000000)) * (((2098175587 / 1000000000000000)) * ((36747942841 / 1000000000000000000))) + ((413788929 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13040) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((440234079 / 100000000000000000000) : ℝ) + ((413788929 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13040

namespace BstLean.Part266.Row13040
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13040 165 ∧
    0 ≤ (tableEnvelope C).f1 13040 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13040 165 ∧
    0 ≤ (tableEnvelope C).w1 13040 165 ∧ 0 ≤ (tableEnvelope C).w2 13040 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13040 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13040 165 ∧ 0 ≤ d.f1 13040 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13040 165 ∧ 0 ≤ d.w1 13040 165 ∧ 0 ≤ d.w2 13040 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13040 ≤ 2 * (228 / 100 : ℝ) / 13040 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13040 ≤ 2 * (370 / 100 : ℝ) / 13040 := by
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
    (completeRAData (tableEnvelope C) 13040 165).locationBound 13040 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13040 165).energyBound 13040 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13040 165) (d.f1 13040 165) d.f2 ≤
      32 * (((2144890449 / 500000000000000000) : ℝ) + (1431143563 / 1000000000000000000) + (343975921 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13040 165) (d.w1 13040 165)
      (d.w2 13040 165) ≤
      32 * (((338700789 / 20000000000000000000) : ℝ) + (1204895741 / 100000000000000000000) + (55029761 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13040 165) (d.f1 13040 165) d.f2 ≤
      ((2144890449 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2144890449 / 500000000000000000)) * ((1431143563 / 1000000000000000000)) * (126 / 100) +
      2 * (((1431143563 / 1000000000000000000)) ^ 2 + 2 * ((2144890449 / 500000000000000000)) * ((343975921 / 1000000000000000000))) +
      6 * ((1431143563 / 1000000000000000000)) * ((343975921 / 1000000000000000000)) * (126 / 100) + 8 * ((343975921 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13040 165) (d.f1 13040 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13040 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13040 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13040 165) (d.f1 13040 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13040 165) (d.w1 13040 165) (d.w2 13040 165)
  have hwexpr0 : 0 ≤ d.w0 13040 165 + d.w1 13040 165 * √(π / 2) +
      2 * d.w2 13040 165 + energyR16 13040 *
      radiusPolynomialRoot16 (d.w0 13040 165) (d.w1 13040 165) (d.w2 13040 165) := by
    positivity
  constructor
  · change (13040 : ℝ) ^ 8 * (mA 13040 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13040 165) (d.f1 13040 165) d.f2 + locationR16 13040 *
        radiusPolynomialRoot16 (d.f0 13040 165) (d.f1 13040 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13040 : ℝ) ^ 8 * (mA 13040 : ℝ) ^ 8 *
        ((((2144890449 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2144890449 / 500000000000000000)) * ((1431143563 / 1000000000000000000)) * (126 / 100) +
          2 * (((1431143563 / 1000000000000000000)) ^ 2 + 2 * ((2144890449 / 500000000000000000)) * ((343975921 / 1000000000000000000))) +
          6 * ((1431143563 / 1000000000000000000)) * ((343975921 / 1000000000000000000)) * (126 / 100) + 8 * ((343975921 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13040) *
          (32 * (((2144890449 / 500000000000000000) : ℝ) + (1431143563 / 1000000000000000000) + (343975921 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13040 : ℝ) ^ 16 *
      (d.w0 13040 165 + d.w1 13040 165 * √(π / 2) + 2 * d.w2 13040 165 +
        energyR16 13040 * radiusPolynomialRoot16 (d.w0 13040 165) (d.w1 13040 165)
          (d.w2 13040 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13040 : ℝ) ^ 16 *
        (((338700789 / 20000000000000000000) : ℝ) + ((1204895741 / 100000000000000000000)) * (126 / 100) + 2 * ((55029761 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13040) *
          (32 * (((338700789 / 20000000000000000000) : ℝ) + (1204895741 / 100000000000000000000) + (55029761 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13040

/-! A coarse bound on the actual paper statistics constant at dimension 13041. -/
namespace BstLean.Part266.Row13041
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13039 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13039 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13039 128 ≤ (13293 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13293 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13041) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13041 : ℕ))
    (by norm_num : (13041 : ℕ) ≤ 16384)
  have ht : paperTail256 13041 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13041 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13041 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13041 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13041 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13041 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13039 128 * √(2 / (13041 : ℝ)) *
      (√(13041 : ℝ) + paperT0 13041 + paperTail256 13041) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13041 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13041 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13041 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13039 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13039 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13041 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13041

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13041
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13041 (61 / 100) 165 (17 / (100 * 13041)) (26 / (10 * 13041)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13041 (61 / 100) 165 (17 / (100 * 13041)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (55016601 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (134999713 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (258457973 / 62500000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13041 / 13041 * (61 / 100)) ^ 4 * inverseRadius8 (13041 - 1) /
            envelopeGap 13041 (61 / 100) 165 (17 / (100 * 13041)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13041

namespace BstLean.Part266.Row13041
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13041 165 ≤ (214448023 / 50000000000000000)
  f1 : (tableEnvelope C).f1 13041 165 ≤ (357717413 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (343910033 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13041 165 ≤ (338622953 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 13041 165 ≤ (301154689 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 13041 165 ≤ (220068407 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (55016601 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (55016601 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (134999713 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (258457973 / 62500000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3610513 / 1000000000) : ℝ) ≤ √(17 / (100 * 13041) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13041) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1048967121 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18371153543 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13041) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13041) ≤ (21688729 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13041) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13041 * (165 : ℝ) ^ 2 + 26 / (10 * 13041) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13041) : ℝ)) (tA 13041 * 165 ^ 2 + 26 / (10 * 13041)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3610513 / 1000000000))) * ((55016601 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3610513 / 1000000000)) ^ 3) * ((134999713 / 100000000000000000000000))) + ((258457973 / 62500000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3610513 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13041) : ℝ)) d.D d.V d.P (√(tA 13041) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3610513 / 1000000000)) ^ 2 * (((1048967121 / 500000000000000)) * ((18371153543 / 500000000000000000)))) + ((258457973 / 62500000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13041) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3610513 / 1000000000)) * ((55016601 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13041) : ℝ)) (tA 13041 * 165 ^ 2 + 26 / (10 * 13041)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((55016601 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3610513 / 1000000000)) ^ 2) * ((134999713 / 100000000000000000000000)) + ((258457973 / 62500000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13041) : ℝ)) (√(26 / (10 * 13041) : ℝ)) d.D d.V d.P (√(tA 13041) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3610513 / 1000000000)) * (((1048967121 / 500000000000000)) * ((18371153543 / 500000000000000000))) + ((258457973 / 62500000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13041) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((55016601 / 12500000000000000000) : ℝ) + ((258457973 / 62500000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13041

namespace BstLean.Part266.Row13041
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13041 165 ∧
    0 ≤ (tableEnvelope C).f1 13041 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13041 165 ∧
    0 ≤ (tableEnvelope C).w1 13041 165 ∧ 0 ≤ (tableEnvelope C).w2 13041 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13041 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13041 165 ∧ 0 ≤ d.f1 13041 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13041 165 ∧ 0 ≤ d.w1 13041 165 ∧ 0 ≤ d.w2 13041 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13041 ≤ 2 * (228 / 100 : ℝ) / 13041 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13041 ≤ 2 * (370 / 100 : ℝ) / 13041 := by
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
    (completeRAData (tableEnvelope C) 13041 165).locationBound 13041 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13041 165).energyBound 13041 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13041 165) (d.f1 13041 165) d.f2 ≤
      32 * (((214448023 / 50000000000000000) : ℝ) + (357717413 / 250000000000000000) + (343910033 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13041 165) (d.w1 13041 165)
      (d.w2 13041 165) ≤
      32 * (((338622953 / 20000000000000000000) : ℝ) + (301154689 / 25000000000000000000) + (220068407 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13041 165) (d.f1 13041 165) d.f2 ≤
      ((214448023 / 50000000000000000) : ℝ) ^ 2 + 2 * ((214448023 / 50000000000000000)) * ((357717413 / 250000000000000000)) * (126 / 100) +
      2 * (((357717413 / 250000000000000000)) ^ 2 + 2 * ((214448023 / 50000000000000000)) * ((343910033 / 1000000000000000000))) +
      6 * ((357717413 / 250000000000000000)) * ((343910033 / 1000000000000000000)) * (126 / 100) + 8 * ((343910033 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13041 165) (d.f1 13041 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13041 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13041 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13041 165) (d.f1 13041 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13041 165) (d.w1 13041 165) (d.w2 13041 165)
  have hwexpr0 : 0 ≤ d.w0 13041 165 + d.w1 13041 165 * √(π / 2) +
      2 * d.w2 13041 165 + energyR16 13041 *
      radiusPolynomialRoot16 (d.w0 13041 165) (d.w1 13041 165) (d.w2 13041 165) := by
    positivity
  constructor
  · change (13041 : ℝ) ^ 8 * (mA 13041 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13041 165) (d.f1 13041 165) d.f2 + locationR16 13041 *
        radiusPolynomialRoot16 (d.f0 13041 165) (d.f1 13041 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13041 : ℝ) ^ 8 * (mA 13041 : ℝ) ^ 8 *
        ((((214448023 / 50000000000000000) : ℝ) ^ 2 + 2 * ((214448023 / 50000000000000000)) * ((357717413 / 250000000000000000)) * (126 / 100) +
          2 * (((357717413 / 250000000000000000)) ^ 2 + 2 * ((214448023 / 50000000000000000)) * ((343910033 / 1000000000000000000))) +
          6 * ((357717413 / 250000000000000000)) * ((343910033 / 1000000000000000000)) * (126 / 100) + 8 * ((343910033 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13041) *
          (32 * (((214448023 / 50000000000000000) : ℝ) + (357717413 / 250000000000000000) + (343910033 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13041 : ℝ) ^ 16 *
      (d.w0 13041 165 + d.w1 13041 165 * √(π / 2) + 2 * d.w2 13041 165 +
        energyR16 13041 * radiusPolynomialRoot16 (d.w0 13041 165) (d.w1 13041 165)
          (d.w2 13041 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13041 : ℝ) ^ 16 *
        (((338622953 / 20000000000000000000) : ℝ) + ((301154689 / 25000000000000000000)) * (126 / 100) + 2 * ((220068407 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13041) *
          (32 * (((338622953 / 20000000000000000000) : ℝ) + (301154689 / 25000000000000000000) + (220068407 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13041

/-! A coarse bound on the actual paper statistics constant at dimension 13042. -/
namespace BstLean.Part266.Row13042
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13040 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13040 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13040 128 ≤ (13294 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13294 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13042) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13042 : ℕ))
    (by norm_num : (13042 : ℕ) ≤ 16384)
  have ht : paperTail256 13042 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13042 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13042 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13042 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13042 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13042 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13040 128 * √(2 / (13042 : ℝ)) *
      (√(13042 : ℝ) + paperT0 13042 + paperTail256 13042) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13042 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13042 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13042 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13040 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13040 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13042 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13042

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13042
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13042 (61 / 100) 165 (17 / (100 * 13042)) (26 / (10 * 13042)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13042 (61 / 100) 165 (17 / (100 * 13042)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (440031569 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (337395779 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4132767633 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13042 / 13042 * (61 / 100)) ^ 4 * inverseRadius8 (13042 - 1) /
            envelopeGap 13042 (61 / 100) 165 (17 / (100 * 13042)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13042

namespace BstLean.Part266.Row13042
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13042 165 ≤ (4288136869 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13042 165 ≤ (357648759 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (343844069 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13042 165 ≤ (846362511 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13042 165 ≤ (1204341529 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13042 165 ≤ (440035573 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (440031569 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (440031569 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (337395779 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4132767633 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((28883 / 8000000) : ℝ) ≤ √(17 / (100 * 13042) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13042) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (419538589 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4592084079 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13042) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13042) ≤ (10843533 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13042) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13042 * (165 : ℝ) ^ 2 + 26 / (10 * 13042) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13042) : ℝ)) (tA 13042 * 165 ^ 2 + 26 / (10 * 13042)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((28883 / 8000000))) * ((440031569 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((28883 / 8000000)) ^ 3) * ((337395779 / 250000000000000000000000))) + ((4132767633 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((28883 / 8000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13042) : ℝ)) d.D d.V d.P (√(tA 13042) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((28883 / 8000000)) ^ 2 * (((419538589 / 200000000000000)) * ((4592084079 / 125000000000000000)))) + ((4132767633 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13042) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((28883 / 8000000)) * ((440031569 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13042) : ℝ)) (tA 13042 * 165 ^ 2 + 26 / (10 * 13042)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((440031569 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((28883 / 8000000)) ^ 2) * ((337395779 / 250000000000000000000000)) + ((4132767633 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13042) : ℝ)) (√(26 / (10 * 13042) : ℝ)) d.D d.V d.P (√(tA 13042) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((28883 / 8000000)) * (((419538589 / 200000000000000)) * ((4592084079 / 125000000000000000))) + ((4132767633 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13042) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((440031569 / 100000000000000000000) : ℝ) + ((4132767633 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13042

namespace BstLean.Part266.Row13042
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13042 165 ∧
    0 ≤ (tableEnvelope C).f1 13042 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13042 165 ∧
    0 ≤ (tableEnvelope C).w1 13042 165 ∧ 0 ≤ (tableEnvelope C).w2 13042 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13042 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13042 165 ∧ 0 ≤ d.f1 13042 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13042 165 ∧ 0 ≤ d.w1 13042 165 ∧ 0 ≤ d.w2 13042 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13042 ≤ 2 * (228 / 100 : ℝ) / 13042 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13042 ≤ 2 * (370 / 100 : ℝ) / 13042 := by
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
    (completeRAData (tableEnvelope C) 13042 165).locationBound 13042 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13042 165).energyBound 13042 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13042 165) (d.f1 13042 165) d.f2 ≤
      32 * (((4288136869 / 1000000000000000000) : ℝ) + (357648759 / 250000000000000000) + (343844069 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13042 165) (d.w1 13042 165)
      (d.w2 13042 165) ≤
      32 * (((846362511 / 50000000000000000000) : ℝ) + (1204341529 / 100000000000000000000) + (440035573 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13042 165) (d.f1 13042 165) d.f2 ≤
      ((4288136869 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4288136869 / 1000000000000000000)) * ((357648759 / 250000000000000000)) * (126 / 100) +
      2 * (((357648759 / 250000000000000000)) ^ 2 + 2 * ((4288136869 / 1000000000000000000)) * ((343844069 / 1000000000000000000))) +
      6 * ((357648759 / 250000000000000000)) * ((343844069 / 1000000000000000000)) * (126 / 100) + 8 * ((343844069 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13042 165) (d.f1 13042 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13042 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13042 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13042 165) (d.f1 13042 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13042 165) (d.w1 13042 165) (d.w2 13042 165)
  have hwexpr0 : 0 ≤ d.w0 13042 165 + d.w1 13042 165 * √(π / 2) +
      2 * d.w2 13042 165 + energyR16 13042 *
      radiusPolynomialRoot16 (d.w0 13042 165) (d.w1 13042 165) (d.w2 13042 165) := by
    positivity
  constructor
  · change (13042 : ℝ) ^ 8 * (mA 13042 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13042 165) (d.f1 13042 165) d.f2 + locationR16 13042 *
        radiusPolynomialRoot16 (d.f0 13042 165) (d.f1 13042 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13042 : ℝ) ^ 8 * (mA 13042 : ℝ) ^ 8 *
        ((((4288136869 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4288136869 / 1000000000000000000)) * ((357648759 / 250000000000000000)) * (126 / 100) +
          2 * (((357648759 / 250000000000000000)) ^ 2 + 2 * ((4288136869 / 1000000000000000000)) * ((343844069 / 1000000000000000000))) +
          6 * ((357648759 / 250000000000000000)) * ((343844069 / 1000000000000000000)) * (126 / 100) + 8 * ((343844069 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13042) *
          (32 * (((4288136869 / 1000000000000000000) : ℝ) + (357648759 / 250000000000000000) + (343844069 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13042 : ℝ) ^ 16 *
      (d.w0 13042 165 + d.w1 13042 165 * √(π / 2) + 2 * d.w2 13042 165 +
        energyR16 13042 * radiusPolynomialRoot16 (d.w0 13042 165) (d.w1 13042 165)
          (d.w2 13042 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13042 : ℝ) ^ 16 *
        (((846362511 / 50000000000000000000) : ℝ) + ((1204341529 / 100000000000000000000)) * (126 / 100) + 2 * ((440035573 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13042) *
          (32 * (((846362511 / 50000000000000000000) : ℝ) + (1204341529 / 100000000000000000000) + (440035573 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13042

/-! A coarse bound on the actual paper statistics constant at dimension 13043. -/
namespace BstLean.Part266.Row13043
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13041 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13041 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13041 128 ≤ (13295 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13295 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13043) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13043 : ℕ))
    (by norm_num : (13043 : ℕ) ≤ 16384)
  have ht : paperTail256 13043 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13043 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13043 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13043 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13043 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13043 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13041 128 * √(2 / (13043 : ℝ)) *
      (√(13043 : ℝ) + paperT0 13043 + paperTail256 13043) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13043 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13043 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13043 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13041 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13041 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13043 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13043

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13043
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13043 (61 / 100) 165 (17 / (100 * 13043)) (26 / (10 * 13043)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13043 (61 / 100) 165 (17 / (100 * 13043)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (439930361 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (67458463 / 50000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2065104741 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13043 / 13043 * (61 / 100)) ^ 4 * inverseRadius8 (13043 - 1) /
            envelopeGap 13043 (61 / 100) 165 (17 / (100 * 13043)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13043

namespace BstLean.Part266.Row13043
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13043 165 ≤ (267957097 / 62500000000000000)
  f1 : (tableEnvelope C).f1 13043 165 ≤ (1430320507 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (110009 / 320000000000000)
  w0 : (tableEnvelope C).w0 13043 165 ≤ (1692335409 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13043 165 ≤ (1204064393 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13043 165 ≤ (219967181 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (439930361 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (439930361 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (67458463 / 50000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2065104741 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3610237 / 1000000000) : ℝ) ≤ √(17 / (100 * 13043) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13043) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (419490339 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36731039463 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13043) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13043) ≤ (13553377 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13043) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13043 * (165 : ℝ) ^ 2 + 26 / (10 * 13043) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13043) : ℝ)) (tA 13043 * 165 ^ 2 + 26 / (10 * 13043)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3610237 / 1000000000))) * ((439930361 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3610237 / 1000000000)) ^ 3) * ((67458463 / 50000000000000000000000))) + ((2065104741 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3610237 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13043) : ℝ)) d.D d.V d.P (√(tA 13043) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3610237 / 1000000000)) ^ 2 * (((419490339 / 200000000000000)) * ((36731039463 / 1000000000000000000)))) + ((2065104741 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13043) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3610237 / 1000000000)) * ((439930361 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13043) : ℝ)) (tA 13043 * 165 ^ 2 + 26 / (10 * 13043)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((439930361 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3610237 / 1000000000)) ^ 2) * ((67458463 / 50000000000000000000000)) + ((2065104741 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13043) : ℝ)) (√(26 / (10 * 13043) : ℝ)) d.D d.V d.P (√(tA 13043) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3610237 / 1000000000)) * (((419490339 / 200000000000000)) * ((36731039463 / 1000000000000000000))) + ((2065104741 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13043) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((439930361 / 100000000000000000000) : ℝ) + ((2065104741 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13043

namespace BstLean.Part266.Row13043
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13043 165 ∧
    0 ≤ (tableEnvelope C).f1 13043 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13043 165 ∧
    0 ≤ (tableEnvelope C).w1 13043 165 ∧ 0 ≤ (tableEnvelope C).w2 13043 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13043 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13043 165 ∧ 0 ≤ d.f1 13043 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13043 165 ∧ 0 ≤ d.w1 13043 165 ∧ 0 ≤ d.w2 13043 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13043 ≤ 2 * (228 / 100 : ℝ) / 13043 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13043 ≤ 2 * (370 / 100 : ℝ) / 13043 := by
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
    (completeRAData (tableEnvelope C) 13043 165).locationBound 13043 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13043 165).energyBound 13043 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13043 165) (d.f1 13043 165) d.f2 ≤
      32 * (((267957097 / 62500000000000000) : ℝ) + (1430320507 / 1000000000000000000) + (110009 / 320000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13043 165) (d.w1 13043 165)
      (d.w2 13043 165) ≤
      32 * (((1692335409 / 100000000000000000000) : ℝ) + (1204064393 / 100000000000000000000) + (219967181 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13043 165) (d.f1 13043 165) d.f2 ≤
      ((267957097 / 62500000000000000) : ℝ) ^ 2 + 2 * ((267957097 / 62500000000000000)) * ((1430320507 / 1000000000000000000)) * (126 / 100) +
      2 * (((1430320507 / 1000000000000000000)) ^ 2 + 2 * ((267957097 / 62500000000000000)) * ((110009 / 320000000000000))) +
      6 * ((1430320507 / 1000000000000000000)) * ((110009 / 320000000000000)) * (126 / 100) + 8 * ((110009 / 320000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13043 165) (d.f1 13043 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13043 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13043 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13043 165) (d.f1 13043 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13043 165) (d.w1 13043 165) (d.w2 13043 165)
  have hwexpr0 : 0 ≤ d.w0 13043 165 + d.w1 13043 165 * √(π / 2) +
      2 * d.w2 13043 165 + energyR16 13043 *
      radiusPolynomialRoot16 (d.w0 13043 165) (d.w1 13043 165) (d.w2 13043 165) := by
    positivity
  constructor
  · change (13043 : ℝ) ^ 8 * (mA 13043 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13043 165) (d.f1 13043 165) d.f2 + locationR16 13043 *
        radiusPolynomialRoot16 (d.f0 13043 165) (d.f1 13043 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13043 : ℝ) ^ 8 * (mA 13043 : ℝ) ^ 8 *
        ((((267957097 / 62500000000000000) : ℝ) ^ 2 + 2 * ((267957097 / 62500000000000000)) * ((1430320507 / 1000000000000000000)) * (126 / 100) +
          2 * (((1430320507 / 1000000000000000000)) ^ 2 + 2 * ((267957097 / 62500000000000000)) * ((110009 / 320000000000000))) +
          6 * ((1430320507 / 1000000000000000000)) * ((110009 / 320000000000000)) * (126 / 100) + 8 * ((110009 / 320000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13043) *
          (32 * (((267957097 / 62500000000000000) : ℝ) + (1430320507 / 1000000000000000000) + (110009 / 320000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13043 : ℝ) ^ 16 *
      (d.w0 13043 165 + d.w1 13043 165 * √(π / 2) + 2 * d.w2 13043 165 +
        energyR16 13043 * radiusPolynomialRoot16 (d.w0 13043 165) (d.w1 13043 165)
          (d.w2 13043 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13043 : ℝ) ^ 16 *
        (((1692335409 / 100000000000000000000) : ℝ) + ((1204064393 / 100000000000000000000)) * (126 / 100) + 2 * ((219967181 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13043) *
          (32 * (((1692335409 / 100000000000000000000) : ℝ) + (1204064393 / 100000000000000000000) + (219967181 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13043

/-! A coarse bound on the actual paper statistics constant at dimension 13044. -/
namespace BstLean.Part266.Row13044
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13042 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13042 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13042 128 ≤ (13296 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13296 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13044) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13044 : ℕ))
    (by norm_num : (13044 : ℕ) ≤ 16384)
  have ht : paperTail256 13044 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13044 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13044 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13044 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13044 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13044 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13042 128 * √(2 / (13044 : ℝ)) *
      (√(13044 : ℝ) + paperT0 13044 + paperTail256 13044) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13044 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13044 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13044 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13042 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13042 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13044 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13044

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13044
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13044 (61 / 100) 165 (17 / (100 * 13044)) (26 / (10 * 13044)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13044 (61 / 100) 165 (17 / (100 * 13044)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (439829183 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1348755563 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2063826557 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13044 / 13044 * (61 / 100)) ^ 4 * inverseRadius8 (13044 - 1) /
            envelopeGap 13044 (61 / 100) 165 (17 / (100 * 13044)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13044

namespace BstLean.Part266.Row13044
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13044 165 ≤ (2143246969 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13044 165 ≤ (715023427 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (171856147 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13044 165 ≤ (84597331 / 5000000000000000000)
  w1 : (tableEnvelope C).w1 13044 165 ≤ (601893839 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13044 165 ≤ (219916591 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (439829183 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (439829183 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1348755563 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2063826557 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1805049 / 500000000) : ℝ) ≤ √(17 / (100 * 13044) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13044) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (262151311 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7345081519 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13044) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13044) ≤ (6776169 / 62500000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13044) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13044 * (165 : ℝ) ^ 2 + 26 / (10 * 13044) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13044) : ℝ)) (tA 13044 * 165 ^ 2 + 26 / (10 * 13044)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1805049 / 500000000))) * ((439829183 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1805049 / 500000000)) ^ 3) * ((1348755563 / 1000000000000000000000000))) + ((2063826557 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1805049 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13044) : ℝ)) d.D d.V d.P (√(tA 13044) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1805049 / 500000000)) ^ 2 * (((262151311 / 125000000000000)) * ((7345081519 / 200000000000000000)))) + ((2063826557 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13044) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1805049 / 500000000)) * ((439829183 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13044) : ℝ)) (tA 13044 * 165 ^ 2 + 26 / (10 * 13044)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((439829183 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1805049 / 500000000)) ^ 2) * ((1348755563 / 1000000000000000000000000)) + ((2063826557 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13044) : ℝ)) (√(26 / (10 * 13044) : ℝ)) d.D d.V d.P (√(tA 13044) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1805049 / 500000000)) * (((262151311 / 125000000000000)) * ((7345081519 / 200000000000000000))) + ((2063826557 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13044) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((439829183 / 100000000000000000000) : ℝ) + ((2063826557 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13044

namespace BstLean.Part266.Row13044
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13044 165 ∧
    0 ≤ (tableEnvelope C).f1 13044 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13044 165 ∧
    0 ≤ (tableEnvelope C).w1 13044 165 ∧ 0 ≤ (tableEnvelope C).w2 13044 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13044 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13044 165 ∧ 0 ≤ d.f1 13044 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13044 165 ∧ 0 ≤ d.w1 13044 165 ∧ 0 ≤ d.w2 13044 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13044 ≤ 2 * (228 / 100 : ℝ) / 13044 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13044 ≤ 2 * (370 / 100 : ℝ) / 13044 := by
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
    (completeRAData (tableEnvelope C) 13044 165).locationBound 13044 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13044 165).energyBound 13044 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13044 165) (d.f1 13044 165) d.f2 ≤
      32 * (((2143246969 / 500000000000000000) : ℝ) + (715023427 / 500000000000000000) + (171856147 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13044 165) (d.w1 13044 165)
      (d.w2 13044 165) ≤
      32 * (((84597331 / 5000000000000000000) : ℝ) + (601893839 / 50000000000000000000) + (219916591 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13044 165) (d.f1 13044 165) d.f2 ≤
      ((2143246969 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2143246969 / 500000000000000000)) * ((715023427 / 500000000000000000)) * (126 / 100) +
      2 * (((715023427 / 500000000000000000)) ^ 2 + 2 * ((2143246969 / 500000000000000000)) * ((171856147 / 500000000000000000))) +
      6 * ((715023427 / 500000000000000000)) * ((171856147 / 500000000000000000)) * (126 / 100) + 8 * ((171856147 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13044 165) (d.f1 13044 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13044 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13044 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13044 165) (d.f1 13044 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13044 165) (d.w1 13044 165) (d.w2 13044 165)
  have hwexpr0 : 0 ≤ d.w0 13044 165 + d.w1 13044 165 * √(π / 2) +
      2 * d.w2 13044 165 + energyR16 13044 *
      radiusPolynomialRoot16 (d.w0 13044 165) (d.w1 13044 165) (d.w2 13044 165) := by
    positivity
  constructor
  · change (13044 : ℝ) ^ 8 * (mA 13044 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13044 165) (d.f1 13044 165) d.f2 + locationR16 13044 *
        radiusPolynomialRoot16 (d.f0 13044 165) (d.f1 13044 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13044 : ℝ) ^ 8 * (mA 13044 : ℝ) ^ 8 *
        ((((2143246969 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2143246969 / 500000000000000000)) * ((715023427 / 500000000000000000)) * (126 / 100) +
          2 * (((715023427 / 500000000000000000)) ^ 2 + 2 * ((2143246969 / 500000000000000000)) * ((171856147 / 500000000000000000))) +
          6 * ((715023427 / 500000000000000000)) * ((171856147 / 500000000000000000)) * (126 / 100) + 8 * ((171856147 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13044) *
          (32 * (((2143246969 / 500000000000000000) : ℝ) + (715023427 / 500000000000000000) + (171856147 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13044 : ℝ) ^ 16 *
      (d.w0 13044 165 + d.w1 13044 165 * √(π / 2) + 2 * d.w2 13044 165 +
        energyR16 13044 * radiusPolynomialRoot16 (d.w0 13044 165) (d.w1 13044 165)
          (d.w2 13044 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13044 : ℝ) ^ 16 *
        (((84597331 / 5000000000000000000) : ℝ) + ((601893839 / 50000000000000000000)) * (126 / 100) + 2 * ((219916591 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13044) *
          (32 * (((84597331 / 5000000000000000000) : ℝ) + (601893839 / 50000000000000000000) + (219916591 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13044

/-! A coarse bound on the actual paper statistics constant at dimension 13045. -/
namespace BstLean.Part266.Row13045
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13043 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13043 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13043 128 ≤ (13297 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13297 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13045) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13045 : ℕ))
    (by norm_num : (13045 : ℕ) ≤ 16384)
  have ht : paperTail256 13045 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13045 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13045 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13045 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13045 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13045 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13043 128 * √(2 / (13045 : ℝ)) *
      (√(13045 : ℝ) + paperT0 13045 + paperTail256 13045) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13045 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13045 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13045 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13043 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13043 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13045 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13045

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13045
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13045 (61 / 100) 165 (17 / (100 * 13045)) (26 / (10 * 13045)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13045 (61 / 100) 165 (17 / (100 * 13045)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (439728037 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (53933681 / 40000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4125098527 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13045 / 13045 * (61 / 100)) ^ 4 * inverseRadius8 (13045 - 1) /
            envelopeGap 13045 (61 / 100) 165 (17 / (100 * 13045)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13045

namespace BstLean.Part266.Row13045
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13045 165 ≤ (2142835587 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13045 165 ≤ (1429772497 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (85911597 / 250000000000000000)
  w0 : (tableEnvelope C).w0 13045 165 ≤ (1691557269 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13045 165 ≤ (601755361 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13045 165 ≤ (439732033 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (439728037 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (439728037 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (53933681 / 40000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4125098527 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((90249 / 25000000) : ℝ) ≤ √(17 / (100 * 13045) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13045) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (209696933 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36719777029 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13045) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13045) ≤ (13551299 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13045) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13045 * (165 : ℝ) ^ 2 + 26 / (10 * 13045) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13045) : ℝ)) (tA 13045 * 165 ^ 2 + 26 / (10 * 13045)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((90249 / 25000000))) * ((439728037 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((90249 / 25000000)) ^ 3) * ((53933681 / 40000000000000000000000))) + ((4125098527 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((90249 / 25000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13045) : ℝ)) d.D d.V d.P (√(tA 13045) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((90249 / 25000000)) ^ 2 * (((209696933 / 100000000000000)) * ((36719777029 / 1000000000000000000)))) + ((4125098527 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13045) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((90249 / 25000000)) * ((439728037 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13045) : ℝ)) (tA 13045 * 165 ^ 2 + 26 / (10 * 13045)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((439728037 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((90249 / 25000000)) ^ 2) * ((53933681 / 40000000000000000000000)) + ((4125098527 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13045) : ℝ)) (√(26 / (10 * 13045) : ℝ)) d.D d.V d.P (√(tA 13045) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((90249 / 25000000)) * (((209696933 / 100000000000000)) * ((36719777029 / 1000000000000000000))) + ((4125098527 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13045) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((439728037 / 100000000000000000000) : ℝ) + ((4125098527 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13045

namespace BstLean.Part266.Row13045
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13045 165 ∧
    0 ≤ (tableEnvelope C).f1 13045 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13045 165 ∧
    0 ≤ (tableEnvelope C).w1 13045 165 ∧ 0 ≤ (tableEnvelope C).w2 13045 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13045 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13045 165 ∧ 0 ≤ d.f1 13045 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13045 165 ∧ 0 ≤ d.w1 13045 165 ∧ 0 ≤ d.w2 13045 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13045 ≤ 2 * (228 / 100 : ℝ) / 13045 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13045 ≤ 2 * (370 / 100 : ℝ) / 13045 := by
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
    (completeRAData (tableEnvelope C) 13045 165).locationBound 13045 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13045 165).energyBound 13045 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13045 165) (d.f1 13045 165) d.f2 ≤
      32 * (((2142835587 / 500000000000000000) : ℝ) + (1429772497 / 1000000000000000000) + (85911597 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13045 165) (d.w1 13045 165)
      (d.w2 13045 165) ≤
      32 * (((1691557269 / 100000000000000000000) : ℝ) + (601755361 / 50000000000000000000) + (439732033 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13045 165) (d.f1 13045 165) d.f2 ≤
      ((2142835587 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2142835587 / 500000000000000000)) * ((1429772497 / 1000000000000000000)) * (126 / 100) +
      2 * (((1429772497 / 1000000000000000000)) ^ 2 + 2 * ((2142835587 / 500000000000000000)) * ((85911597 / 250000000000000000))) +
      6 * ((1429772497 / 1000000000000000000)) * ((85911597 / 250000000000000000)) * (126 / 100) + 8 * ((85911597 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13045 165) (d.f1 13045 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13045 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13045 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13045 165) (d.f1 13045 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13045 165) (d.w1 13045 165) (d.w2 13045 165)
  have hwexpr0 : 0 ≤ d.w0 13045 165 + d.w1 13045 165 * √(π / 2) +
      2 * d.w2 13045 165 + energyR16 13045 *
      radiusPolynomialRoot16 (d.w0 13045 165) (d.w1 13045 165) (d.w2 13045 165) := by
    positivity
  constructor
  · change (13045 : ℝ) ^ 8 * (mA 13045 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13045 165) (d.f1 13045 165) d.f2 + locationR16 13045 *
        radiusPolynomialRoot16 (d.f0 13045 165) (d.f1 13045 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13045 : ℝ) ^ 8 * (mA 13045 : ℝ) ^ 8 *
        ((((2142835587 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2142835587 / 500000000000000000)) * ((1429772497 / 1000000000000000000)) * (126 / 100) +
          2 * (((1429772497 / 1000000000000000000)) ^ 2 + 2 * ((2142835587 / 500000000000000000)) * ((85911597 / 250000000000000000))) +
          6 * ((1429772497 / 1000000000000000000)) * ((85911597 / 250000000000000000)) * (126 / 100) + 8 * ((85911597 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13045) *
          (32 * (((2142835587 / 500000000000000000) : ℝ) + (1429772497 / 1000000000000000000) + (85911597 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13045 : ℝ) ^ 16 *
      (d.w0 13045 165 + d.w1 13045 165 * √(π / 2) + 2 * d.w2 13045 165 +
        energyR16 13045 * radiusPolynomialRoot16 (d.w0 13045 165) (d.w1 13045 165)
          (d.w2 13045 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13045 : ℝ) ^ 16 *
        (((1691557269 / 100000000000000000000) : ℝ) + ((601755361 / 50000000000000000000)) * (126 / 100) + 2 * ((439732033 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13045) *
          (32 * (((1691557269 / 100000000000000000000) : ℝ) + (601755361 / 50000000000000000000) + (439732033 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13045

/-! A coarse bound on the actual paper statistics constant at dimension 13046. -/
namespace BstLean.Part266.Row13046
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13044 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13044 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13044 128 ≤ (13298 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13298 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13046) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13046 : ℕ))
    (by norm_num : (13046 : ℕ) ≤ 16384)
  have ht : paperTail256 13046 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13046 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13046 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13046 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13046 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13046 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13044 128 * √(2 / (13046 : ℝ)) *
      (√(13046 : ℝ) + paperT0 13046 + paperTail256 13046) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13046 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13046 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13046 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13044 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13044 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13046 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13046

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13046
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13046 (61 / 100) 165 (17 / (100 * 13046)) (26 / (10 * 13046)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13046 (61 / 100) 165 (17 / (100 * 13046)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (219813461 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (269585729 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4122545721 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13046 / 13046 * (61 / 100)) ^ 4 * inverseRadius8 (13046 - 1) /
            envelopeGap 13046 (61 / 100) 165 (17 / (100 * 13046)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13046

namespace BstLean.Part266.Row13046
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13046 165 ≤ (428485211 / 100000000000000000)
  f1 : (tableEnvelope C).f1 13046 165 ≤ (714749509 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (85895149 / 250000000000000000)
  w0 : (tableEnvelope C).w0 13046 165 ≤ (1691168741 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13046 165 ≤ (120323419 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 13046 165 ≤ (109907729 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (219813461 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (219813461 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (269585729 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4122545721 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3609821 / 1000000000) : ℝ) ≤ √(17 / (100 * 13046) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13046) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1048364109 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (146856591 / 4000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13046) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13046) ≤ (108402083 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13046) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13046 * (165 : ℝ) ^ 2 + 26 / (10 * 13046) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13046) : ℝ)) (tA 13046 * 165 ^ 2 + 26 / (10 * 13046)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3609821 / 1000000000))) * ((219813461 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3609821 / 1000000000)) ^ 3) * ((269585729 / 200000000000000000000000))) + ((4122545721 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3609821 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13046) : ℝ)) d.D d.V d.P (√(tA 13046) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3609821 / 1000000000)) ^ 2 * (((1048364109 / 500000000000000)) * ((146856591 / 4000000000000000)))) + ((4122545721 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13046) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3609821 / 1000000000)) * ((219813461 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13046) : ℝ)) (tA 13046 * 165 ^ 2 + 26 / (10 * 13046)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((219813461 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3609821 / 1000000000)) ^ 2) * ((269585729 / 200000000000000000000000)) + ((4122545721 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13046) : ℝ)) (√(26 / (10 * 13046) : ℝ)) d.D d.V d.P (√(tA 13046) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3609821 / 1000000000)) * (((1048364109 / 500000000000000)) * ((146856591 / 4000000000000000))) + ((4122545721 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13046) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((219813461 / 50000000000000000000) : ℝ) + ((4122545721 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13046

namespace BstLean.Part266.Row13046
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13046 165 ∧
    0 ≤ (tableEnvelope C).f1 13046 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13046 165 ∧
    0 ≤ (tableEnvelope C).w1 13046 165 ∧ 0 ≤ (tableEnvelope C).w2 13046 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13046 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13046 165 ∧ 0 ≤ d.f1 13046 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13046 165 ∧ 0 ≤ d.w1 13046 165 ∧ 0 ≤ d.w2 13046 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13046 ≤ 2 * (228 / 100 : ℝ) / 13046 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13046 ≤ 2 * (370 / 100 : ℝ) / 13046 := by
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
    (completeRAData (tableEnvelope C) 13046 165).locationBound 13046 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13046 165).energyBound 13046 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13046 165) (d.f1 13046 165) d.f2 ≤
      32 * (((428485211 / 100000000000000000) : ℝ) + (714749509 / 500000000000000000) + (85895149 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13046 165) (d.w1 13046 165)
      (d.w2 13046 165) ≤
      32 * (((1691168741 / 100000000000000000000) : ℝ) + (120323419 / 10000000000000000000) + (109907729 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13046 165) (d.f1 13046 165) d.f2 ≤
      ((428485211 / 100000000000000000) : ℝ) ^ 2 + 2 * ((428485211 / 100000000000000000)) * ((714749509 / 500000000000000000)) * (126 / 100) +
      2 * (((714749509 / 500000000000000000)) ^ 2 + 2 * ((428485211 / 100000000000000000)) * ((85895149 / 250000000000000000))) +
      6 * ((714749509 / 500000000000000000)) * ((85895149 / 250000000000000000)) * (126 / 100) + 8 * ((85895149 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13046 165) (d.f1 13046 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13046 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13046 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13046 165) (d.f1 13046 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13046 165) (d.w1 13046 165) (d.w2 13046 165)
  have hwexpr0 : 0 ≤ d.w0 13046 165 + d.w1 13046 165 * √(π / 2) +
      2 * d.w2 13046 165 + energyR16 13046 *
      radiusPolynomialRoot16 (d.w0 13046 165) (d.w1 13046 165) (d.w2 13046 165) := by
    positivity
  constructor
  · change (13046 : ℝ) ^ 8 * (mA 13046 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13046 165) (d.f1 13046 165) d.f2 + locationR16 13046 *
        radiusPolynomialRoot16 (d.f0 13046 165) (d.f1 13046 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13046 : ℝ) ^ 8 * (mA 13046 : ℝ) ^ 8 *
        ((((428485211 / 100000000000000000) : ℝ) ^ 2 + 2 * ((428485211 / 100000000000000000)) * ((714749509 / 500000000000000000)) * (126 / 100) +
          2 * (((714749509 / 500000000000000000)) ^ 2 + 2 * ((428485211 / 100000000000000000)) * ((85895149 / 250000000000000000))) +
          6 * ((714749509 / 500000000000000000)) * ((85895149 / 250000000000000000)) * (126 / 100) + 8 * ((85895149 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13046) *
          (32 * (((428485211 / 100000000000000000) : ℝ) + (714749509 / 500000000000000000) + (85895149 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13046 : ℝ) ^ 16 *
      (d.w0 13046 165 + d.w1 13046 165 * √(π / 2) + 2 * d.w2 13046 165 +
        energyR16 13046 * radiusPolynomialRoot16 (d.w0 13046 165) (d.w1 13046 165)
          (d.w2 13046 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13046 : ℝ) ^ 16 *
        (((1691168741 / 100000000000000000000) : ℝ) + ((120323419 / 10000000000000000000)) * (126 / 100) + 2 * ((109907729 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13046) *
          (32 * (((1691168741 / 100000000000000000000) : ℝ) + (120323419 / 10000000000000000000) + (109907729 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13046

/-! A coarse bound on the actual paper statistics constant at dimension 13047. -/
namespace BstLean.Part266.Row13047
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13045 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13045 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13045 128 ≤ (13299 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13299 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13047) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13047 : ℕ))
    (by norm_num : (13047 : ℕ) ≤ 16384)
  have ht : paperTail256 13047 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13047 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13047 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13047 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13047 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13047 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13045 128 * √(2 / (13047 : ℝ)) *
      (√(13047 : ℝ) + paperT0 13047 + paperTail256 13047) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13047 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13047 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13047 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13045 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13045 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13047 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13047

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13047
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13047 (61 / 100) 165 (17 / (100 * 13047)) (26 / (10 * 13047)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13047 (61 / 100) 165 (17 / (100 * 13047)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (439525837 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (42109857 / 31250000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2059997347 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13047 / 13047 * (61 / 100)) ^ 4 * inverseRadius8 (13047 - 1) /
            envelopeGap 13047 (61 / 100) 165 (17 / (100 * 13047)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13047

namespace BstLean.Part266.Row13047
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13047 165 ≤ (856805979 / 200000000000000000)
  f1 : (tableEnvelope C).f1 13047 165 ≤ (11165819 / 7812500000000000)
  f2 : (tableEnvelope C).f2 ≤ (343514727 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13047 165 ≤ (33815593 / 2000000000000000000)
  w1 : (tableEnvelope C).w1 13047 165 ≤ (1202957413 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13047 165 ≤ (109882457 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (439525837 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (439525837 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (42109857 / 31250000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2059997347 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3609683 / 1000000000) : ℝ) ≤ √(17 / (100 * 13047) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13047) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (41929743 / 20000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1468340791 / 40000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13047) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13047) ≤ (54196887 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13047) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13047 * (165 : ℝ) ^ 2 + 26 / (10 * 13047) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13047) : ℝ)) (tA 13047 * 165 ^ 2 + 26 / (10 * 13047)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3609683 / 1000000000))) * ((439525837 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3609683 / 1000000000)) ^ 3) * ((42109857 / 31250000000000000000000))) + ((2059997347 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3609683 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13047) : ℝ)) d.D d.V d.P (√(tA 13047) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3609683 / 1000000000)) ^ 2 * (((41929743 / 20000000000000)) * ((1468340791 / 40000000000000000)))) + ((2059997347 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13047) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3609683 / 1000000000)) * ((439525837 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13047) : ℝ)) (tA 13047 * 165 ^ 2 + 26 / (10 * 13047)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((439525837 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3609683 / 1000000000)) ^ 2) * ((42109857 / 31250000000000000000000)) + ((2059997347 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13047) : ℝ)) (√(26 / (10 * 13047) : ℝ)) d.D d.V d.P (√(tA 13047) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3609683 / 1000000000)) * (((41929743 / 20000000000000)) * ((1468340791 / 40000000000000000))) + ((2059997347 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13047) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((439525837 / 100000000000000000000) : ℝ) + ((2059997347 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13047

namespace BstLean.Part266.Row13047
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13047 165 ∧
    0 ≤ (tableEnvelope C).f1 13047 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13047 165 ∧
    0 ≤ (tableEnvelope C).w1 13047 165 ∧ 0 ≤ (tableEnvelope C).w2 13047 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13047 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13047 165 ∧ 0 ≤ d.f1 13047 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13047 165 ∧ 0 ≤ d.w1 13047 165 ∧ 0 ≤ d.w2 13047 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13047 ≤ 2 * (228 / 100 : ℝ) / 13047 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13047 ≤ 2 * (370 / 100 : ℝ) / 13047 := by
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
    (completeRAData (tableEnvelope C) 13047 165).locationBound 13047 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13047 165).energyBound 13047 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13047 165) (d.f1 13047 165) d.f2 ≤
      32 * (((856805979 / 200000000000000000) : ℝ) + (11165819 / 7812500000000000) + (343514727 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13047 165) (d.w1 13047 165)
      (d.w2 13047 165) ≤
      32 * (((33815593 / 2000000000000000000) : ℝ) + (1202957413 / 100000000000000000000) + (109882457 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13047 165) (d.f1 13047 165) d.f2 ≤
      ((856805979 / 200000000000000000) : ℝ) ^ 2 + 2 * ((856805979 / 200000000000000000)) * ((11165819 / 7812500000000000)) * (126 / 100) +
      2 * (((11165819 / 7812500000000000)) ^ 2 + 2 * ((856805979 / 200000000000000000)) * ((343514727 / 1000000000000000000))) +
      6 * ((11165819 / 7812500000000000)) * ((343514727 / 1000000000000000000)) * (126 / 100) + 8 * ((343514727 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13047 165) (d.f1 13047 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13047 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13047 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13047 165) (d.f1 13047 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13047 165) (d.w1 13047 165) (d.w2 13047 165)
  have hwexpr0 : 0 ≤ d.w0 13047 165 + d.w1 13047 165 * √(π / 2) +
      2 * d.w2 13047 165 + energyR16 13047 *
      radiusPolynomialRoot16 (d.w0 13047 165) (d.w1 13047 165) (d.w2 13047 165) := by
    positivity
  constructor
  · change (13047 : ℝ) ^ 8 * (mA 13047 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13047 165) (d.f1 13047 165) d.f2 + locationR16 13047 *
        radiusPolynomialRoot16 (d.f0 13047 165) (d.f1 13047 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13047 : ℝ) ^ 8 * (mA 13047 : ℝ) ^ 8 *
        ((((856805979 / 200000000000000000) : ℝ) ^ 2 + 2 * ((856805979 / 200000000000000000)) * ((11165819 / 7812500000000000)) * (126 / 100) +
          2 * (((11165819 / 7812500000000000)) ^ 2 + 2 * ((856805979 / 200000000000000000)) * ((343514727 / 1000000000000000000))) +
          6 * ((11165819 / 7812500000000000)) * ((343514727 / 1000000000000000000)) * (126 / 100) + 8 * ((343514727 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13047) *
          (32 * (((856805979 / 200000000000000000) : ℝ) + (11165819 / 7812500000000000) + (343514727 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13047 : ℝ) ^ 16 *
      (d.w0 13047 165 + d.w1 13047 165 * √(π / 2) + 2 * d.w2 13047 165 +
        energyR16 13047 * radiusPolynomialRoot16 (d.w0 13047 165) (d.w1 13047 165)
          (d.w2 13047 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13047 : ℝ) ^ 16 *
        (((33815593 / 2000000000000000000) : ℝ) + ((1202957413 / 100000000000000000000)) * (126 / 100) + 2 * ((109882457 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13047) *
          (32 * (((33815593 / 2000000000000000000) : ℝ) + (1202957413 / 100000000000000000000) + (109882457 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13047

/-! A coarse bound on the actual paper statistics constant at dimension 13048. -/
namespace BstLean.Part266.Row13048
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13046 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13046 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13046 128 ≤ (13300 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13300 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13048) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13048 : ℕ))
    (by norm_num : (13048 : ℕ) ≤ 16384)
  have ht : paperTail256 13048 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13048 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13048 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13048 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13048 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13048 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13046 128 * √(2 / (13048 : ℝ)) *
      (√(13048 : ℝ) + paperT0 13048 + paperTail256 13048) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13048 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13048 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13048 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13046 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13046 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13048 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13048

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13048
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13048 (61 / 100) 165 (17 / (100 * 13048)) (26 / (10 * 13048)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13048 (61 / 100) 165 (17 / (100 * 13048)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (27464049 / 6250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (33677559 / 25000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (823489089 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13048 / 13048 * (61 / 100)) ^ 4 * inverseRadius8 (13048 - 1) /
            envelopeGap 13048 (61 / 100) 165 (17 / (100 * 13048)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13048

namespace BstLean.Part266.Row13048
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13048 165 ≤ (267700497 / 62500000000000000)
  f1 : (tableEnvelope C).f1 13048 165 ≤ (714475367 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (343448879 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13048 165 ≤ (1690390689 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13048 165 ≤ (1202680727 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13048 165 ≤ (439428773 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (27464049 / 6250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (27464049 / 6250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (33677559 / 25000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (823489089 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((721909 / 200000000) : ℝ) ≤ √(17 / (100 * 13048) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13048) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2096246131 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18351446537 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13048) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13048) ≤ (108385467 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13048) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13048 * (165 : ℝ) ^ 2 + 26 / (10 * 13048) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13048) : ℝ)) (tA 13048 * 165 ^ 2 + 26 / (10 * 13048)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((721909 / 200000000))) * ((27464049 / 6250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((721909 / 200000000)) ^ 3) * ((33677559 / 25000000000000000000000))) + ((823489089 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((721909 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13048) : ℝ)) d.D d.V d.P (√(tA 13048) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((721909 / 200000000)) ^ 2 * (((2096246131 / 1000000000000000)) * ((18351446537 / 500000000000000000)))) + ((823489089 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13048) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((721909 / 200000000)) * ((27464049 / 6250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13048) : ℝ)) (tA 13048 * 165 ^ 2 + 26 / (10 * 13048)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((27464049 / 6250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((721909 / 200000000)) ^ 2) * ((33677559 / 25000000000000000000000)) + ((823489089 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13048) : ℝ)) (√(26 / (10 * 13048) : ℝ)) d.D d.V d.P (√(tA 13048) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((721909 / 200000000)) * (((2096246131 / 1000000000000000)) * ((18351446537 / 500000000000000000))) + ((823489089 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13048) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((27464049 / 6250000000000000000) : ℝ) + ((823489089 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13048

namespace BstLean.Part266.Row13048
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13048 165 ∧
    0 ≤ (tableEnvelope C).f1 13048 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13048 165 ∧
    0 ≤ (tableEnvelope C).w1 13048 165 ∧ 0 ≤ (tableEnvelope C).w2 13048 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13048 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13048 165 ∧ 0 ≤ d.f1 13048 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13048 165 ∧ 0 ≤ d.w1 13048 165 ∧ 0 ≤ d.w2 13048 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13048 ≤ 2 * (228 / 100 : ℝ) / 13048 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13048 ≤ 2 * (370 / 100 : ℝ) / 13048 := by
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
    (completeRAData (tableEnvelope C) 13048 165).locationBound 13048 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13048 165).energyBound 13048 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13048 165) (d.f1 13048 165) d.f2 ≤
      32 * (((267700497 / 62500000000000000) : ℝ) + (714475367 / 500000000000000000) + (343448879 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13048 165) (d.w1 13048 165)
      (d.w2 13048 165) ≤
      32 * (((1690390689 / 100000000000000000000) : ℝ) + (1202680727 / 100000000000000000000) + (439428773 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13048 165) (d.f1 13048 165) d.f2 ≤
      ((267700497 / 62500000000000000) : ℝ) ^ 2 + 2 * ((267700497 / 62500000000000000)) * ((714475367 / 500000000000000000)) * (126 / 100) +
      2 * (((714475367 / 500000000000000000)) ^ 2 + 2 * ((267700497 / 62500000000000000)) * ((343448879 / 1000000000000000000))) +
      6 * ((714475367 / 500000000000000000)) * ((343448879 / 1000000000000000000)) * (126 / 100) + 8 * ((343448879 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13048 165) (d.f1 13048 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13048 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13048 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13048 165) (d.f1 13048 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13048 165) (d.w1 13048 165) (d.w2 13048 165)
  have hwexpr0 : 0 ≤ d.w0 13048 165 + d.w1 13048 165 * √(π / 2) +
      2 * d.w2 13048 165 + energyR16 13048 *
      radiusPolynomialRoot16 (d.w0 13048 165) (d.w1 13048 165) (d.w2 13048 165) := by
    positivity
  constructor
  · change (13048 : ℝ) ^ 8 * (mA 13048 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13048 165) (d.f1 13048 165) d.f2 + locationR16 13048 *
        radiusPolynomialRoot16 (d.f0 13048 165) (d.f1 13048 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13048 : ℝ) ^ 8 * (mA 13048 : ℝ) ^ 8 *
        ((((267700497 / 62500000000000000) : ℝ) ^ 2 + 2 * ((267700497 / 62500000000000000)) * ((714475367 / 500000000000000000)) * (126 / 100) +
          2 * (((714475367 / 500000000000000000)) ^ 2 + 2 * ((267700497 / 62500000000000000)) * ((343448879 / 1000000000000000000))) +
          6 * ((714475367 / 500000000000000000)) * ((343448879 / 1000000000000000000)) * (126 / 100) + 8 * ((343448879 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13048) *
          (32 * (((267700497 / 62500000000000000) : ℝ) + (714475367 / 500000000000000000) + (343448879 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13048 : ℝ) ^ 16 *
      (d.w0 13048 165 + d.w1 13048 165 * √(π / 2) + 2 * d.w2 13048 165 +
        energyR16 13048 * radiusPolynomialRoot16 (d.w0 13048 165) (d.w1 13048 165)
          (d.w2 13048 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13048 : ℝ) ^ 16 *
        (((1690390689 / 100000000000000000000) : ℝ) + ((1202680727 / 100000000000000000000)) * (126 / 100) + 2 * ((439428773 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13048) *
          (32 * (((1690390689 / 100000000000000000000) : ℝ) + (1202680727 / 100000000000000000000) + (439428773 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13048

/-! A coarse bound on the actual paper statistics constant at dimension 13049. -/
namespace BstLean.Part266.Row13049
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13047 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13047 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13047 128 ≤ (13301 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13301 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13049) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13049 : ℕ))
    (by norm_num : (13049 : ℕ) ≤ 16384)
  have ht : paperTail256 13049 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13049 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13049 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13049 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13049 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13049 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13047 128 * √(2 / (13049 : ℝ)) *
      (√(13049 : ℝ) + paperT0 13049 + paperTail256 13049) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13049 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13049 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13049 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13047 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13047 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13049 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13049

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13049
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13049 (61 / 100) 165 (17 / (100 * 13049)) (26 / (10 * 13049)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13049 (61 / 100) 165 (17 / (100 * 13049)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (219661881 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (269337891 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4114897971 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13049 / 13049 * (61 / 100)) ^ 4 * inverseRadius8 (13049 - 1) /
            envelopeGap 13049 (61 / 100) 165 (17 / (100 * 13049)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13049

namespace BstLean.Part266.Row13049
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13049 165 ≤ (4282389711 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13049 165 ≤ (1428677513 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (68676629 / 200000000000000000)
  w0 : (tableEnvelope C).w0 13049 165 ≤ (1690002551 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13049 165 ≤ (240480893 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 13049 165 ≤ (439327749 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (219661881 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (219661881 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (269337891 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4114897971 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1804703 / 500000000) : ℝ) ≤ √(17 / (100 * 13049) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13049) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1048002579 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18348633839 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13049) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13049) ≤ (108377161 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13049) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13049 * (165 : ℝ) ^ 2 + 26 / (10 * 13049) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13049) : ℝ)) (tA 13049 * 165 ^ 2 + 26 / (10 * 13049)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1804703 / 500000000))) * ((219661881 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1804703 / 500000000)) ^ 3) * ((269337891 / 200000000000000000000000))) + ((4114897971 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1804703 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13049) : ℝ)) d.D d.V d.P (√(tA 13049) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1804703 / 500000000)) ^ 2 * (((1048002579 / 500000000000000)) * ((18348633839 / 500000000000000000)))) + ((4114897971 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13049) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1804703 / 500000000)) * ((219661881 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13049) : ℝ)) (tA 13049 * 165 ^ 2 + 26 / (10 * 13049)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((219661881 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1804703 / 500000000)) ^ 2) * ((269337891 / 200000000000000000000000)) + ((4114897971 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13049) : ℝ)) (√(26 / (10 * 13049) : ℝ)) d.D d.V d.P (√(tA 13049) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1804703 / 500000000)) * (((1048002579 / 500000000000000)) * ((18348633839 / 500000000000000000))) + ((4114897971 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13049) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((219661881 / 50000000000000000000) : ℝ) + ((4114897971 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13049

namespace BstLean.Part266.Row13049
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13049 165 ∧
    0 ≤ (tableEnvelope C).f1 13049 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13049 165 ∧
    0 ≤ (tableEnvelope C).w1 13049 165 ∧ 0 ≤ (tableEnvelope C).w2 13049 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13049 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13049 165 ∧ 0 ≤ d.f1 13049 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13049 165 ∧ 0 ≤ d.w1 13049 165 ∧ 0 ≤ d.w2 13049 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13049 ≤ 2 * (228 / 100 : ℝ) / 13049 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13049 ≤ 2 * (370 / 100 : ℝ) / 13049 := by
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
    (completeRAData (tableEnvelope C) 13049 165).locationBound 13049 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13049 165).energyBound 13049 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13049 165) (d.f1 13049 165) d.f2 ≤
      32 * (((4282389711 / 1000000000000000000) : ℝ) + (1428677513 / 1000000000000000000) + (68676629 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13049 165) (d.w1 13049 165)
      (d.w2 13049 165) ≤
      32 * (((1690002551 / 100000000000000000000) : ℝ) + (240480893 / 20000000000000000000) + (439327749 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13049 165) (d.f1 13049 165) d.f2 ≤
      ((4282389711 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4282389711 / 1000000000000000000)) * ((1428677513 / 1000000000000000000)) * (126 / 100) +
      2 * (((1428677513 / 1000000000000000000)) ^ 2 + 2 * ((4282389711 / 1000000000000000000)) * ((68676629 / 200000000000000000))) +
      6 * ((1428677513 / 1000000000000000000)) * ((68676629 / 200000000000000000)) * (126 / 100) + 8 * ((68676629 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13049 165) (d.f1 13049 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13049 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13049 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13049 165) (d.f1 13049 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13049 165) (d.w1 13049 165) (d.w2 13049 165)
  have hwexpr0 : 0 ≤ d.w0 13049 165 + d.w1 13049 165 * √(π / 2) +
      2 * d.w2 13049 165 + energyR16 13049 *
      radiusPolynomialRoot16 (d.w0 13049 165) (d.w1 13049 165) (d.w2 13049 165) := by
    positivity
  constructor
  · change (13049 : ℝ) ^ 8 * (mA 13049 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13049 165) (d.f1 13049 165) d.f2 + locationR16 13049 *
        radiusPolynomialRoot16 (d.f0 13049 165) (d.f1 13049 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13049 : ℝ) ^ 8 * (mA 13049 : ℝ) ^ 8 *
        ((((4282389711 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4282389711 / 1000000000000000000)) * ((1428677513 / 1000000000000000000)) * (126 / 100) +
          2 * (((1428677513 / 1000000000000000000)) ^ 2 + 2 * ((4282389711 / 1000000000000000000)) * ((68676629 / 200000000000000000))) +
          6 * ((1428677513 / 1000000000000000000)) * ((68676629 / 200000000000000000)) * (126 / 100) + 8 * ((68676629 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13049) *
          (32 * (((4282389711 / 1000000000000000000) : ℝ) + (1428677513 / 1000000000000000000) + (68676629 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13049 : ℝ) ^ 16 *
      (d.w0 13049 165 + d.w1 13049 165 * √(π / 2) + 2 * d.w2 13049 165 +
        energyR16 13049 * radiusPolynomialRoot16 (d.w0 13049 165) (d.w1 13049 165)
          (d.w2 13049 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13049 : ℝ) ^ 16 *
        (((1690002551 / 100000000000000000000) : ℝ) + ((240480893 / 20000000000000000000)) * (126 / 100) + 2 * ((439327749 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13049) *
          (32 * (((1690002551 / 100000000000000000000) : ℝ) + (240480893 / 20000000000000000000) + (439327749 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13049
