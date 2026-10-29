import BstLean.Part266Shard23Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12925. -/
namespace BstLean.Part266.Row12925
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12923 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12923 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12923 128 ≤ (13177 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13177 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12925) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12925 : ℕ))
    (by norm_num : (12925 : ℕ) ≤ 16384)
  have ht : paperTail256 12925 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12925 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12925 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12925 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12925 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12925 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12923 128 * √(2 / (12925 : ℝ)) *
      (√(12925 : ℝ) + paperT0 12925 + paperTail256 12925) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12925 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12925 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12925 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12923 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12923 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12925 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12925

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12925
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12925 (61 / 100) 164 (17 / (100 * 12925)) (26 / (10 * 12925)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12925 (61 / 100) 164 (17 / (100 * 12925)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (452090489 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (8744497 / 6250000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2221374353 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12925 / 12925 * (61 / 100)) ^ 4 * inverseRadius8 (12925 - 1) /
            envelopeGap 12925 (61 / 100) 164 (17 / (100 * 12925)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12925

namespace BstLean.Part266.Row12925
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12925 164 ≤ (438584627 / 100000000000000000)
  f1 : (tableEnvelope C).f1 12925 164 ≤ (1463192511 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (70335773 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12925 164 ≤ (869556871 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12925 164 ≤ (1237346193 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12925 164 ≤ (452094793 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (452090489 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (452090489 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (8744497 / 6250000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2221374353 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3626679 / 1000000000) : ℝ) ≤ √(17 / (100 * 12925) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12925) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (425248393 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37404806109 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12925) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12925) ≤ (109416911 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12925) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12925 * (164 : ℝ) ^ 2 + 26 / (10 * 12925) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12925) : ℝ)) (tA 12925 * 164 ^ 2 + 26 / (10 * 12925)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3626679 / 1000000000))) * ((452090489 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3626679 / 1000000000)) ^ 3) * ((8744497 / 6250000000000000000000))) + ((2221374353 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3626679 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12925) : ℝ)) d.D d.V d.P (√(tA 12925) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3626679 / 1000000000)) ^ 2 * (((425248393 / 200000000000000)) * ((37404806109 / 1000000000000000000)))) + ((2221374353 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12925) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3626679 / 1000000000)) * ((452090489 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12925) : ℝ)) (tA 12925 * 164 ^ 2 + 26 / (10 * 12925)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((452090489 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3626679 / 1000000000)) ^ 2) * ((8744497 / 6250000000000000000000)) + ((2221374353 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12925) : ℝ)) (√(26 / (10 * 12925) : ℝ)) d.D d.V d.P (√(tA 12925) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3626679 / 1000000000)) * (((425248393 / 200000000000000)) * ((37404806109 / 1000000000000000000))) + ((2221374353 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12925) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((452090489 / 100000000000000000000) : ℝ) + ((2221374353 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12925

namespace BstLean.Part266.Row12925
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12925 164 ∧
    0 ≤ (tableEnvelope C).f1 12925 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12925 164 ∧
    0 ≤ (tableEnvelope C).w1 12925 164 ∧ 0 ≤ (tableEnvelope C).w2 12925 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12925 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12925 164 ∧ 0 ≤ d.f1 12925 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12925 164 ∧ 0 ≤ d.w1 12925 164 ∧ 0 ≤ d.w2 12925 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12925 ≤ 2 * (228 / 100 : ℝ) / 12925 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12925 ≤ 2 * (370 / 100 : ℝ) / 12925 := by
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
    (completeRAData (tableEnvelope C) 12925 164).locationBound 12925 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12925 164).energyBound 12925 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12925 164) (d.f1 12925 164) d.f2 ≤
      32 * (((438584627 / 100000000000000000) : ℝ) + (1463192511 / 1000000000000000000) + (70335773 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12925 164) (d.w1 12925 164)
      (d.w2 12925 164) ≤
      32 * (((869556871 / 50000000000000000000) : ℝ) + (1237346193 / 100000000000000000000) + (452094793 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12925 164) (d.f1 12925 164) d.f2 ≤
      ((438584627 / 100000000000000000) : ℝ) ^ 2 + 2 * ((438584627 / 100000000000000000)) * ((1463192511 / 1000000000000000000)) * (126 / 100) +
      2 * (((1463192511 / 1000000000000000000)) ^ 2 + 2 * ((438584627 / 100000000000000000)) * ((70335773 / 200000000000000000))) +
      6 * ((1463192511 / 1000000000000000000)) * ((70335773 / 200000000000000000)) * (126 / 100) + 8 * ((70335773 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12925 164) (d.f1 12925 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12925 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12925 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12925 164) (d.f1 12925 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12925 164) (d.w1 12925 164) (d.w2 12925 164)
  have hwexpr0 : 0 ≤ d.w0 12925 164 + d.w1 12925 164 * √(π / 2) +
      2 * d.w2 12925 164 + energyR16 12925 *
      radiusPolynomialRoot16 (d.w0 12925 164) (d.w1 12925 164) (d.w2 12925 164) := by
    positivity
  constructor
  · change (12925 : ℝ) ^ 8 * (mA 12925 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12925 164) (d.f1 12925 164) d.f2 + locationR16 12925 *
        radiusPolynomialRoot16 (d.f0 12925 164) (d.f1 12925 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12925 : ℝ) ^ 8 * (mA 12925 : ℝ) ^ 8 *
        ((((438584627 / 100000000000000000) : ℝ) ^ 2 + 2 * ((438584627 / 100000000000000000)) * ((1463192511 / 1000000000000000000)) * (126 / 100) +
          2 * (((1463192511 / 1000000000000000000)) ^ 2 + 2 * ((438584627 / 100000000000000000)) * ((70335773 / 200000000000000000))) +
          6 * ((1463192511 / 1000000000000000000)) * ((70335773 / 200000000000000000)) * (126 / 100) + 8 * ((70335773 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12925) *
          (32 * (((438584627 / 100000000000000000) : ℝ) + (1463192511 / 1000000000000000000) + (70335773 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12925 : ℝ) ^ 16 *
      (d.w0 12925 164 + d.w1 12925 164 * √(π / 2) + 2 * d.w2 12925 164 +
        energyR16 12925 * radiusPolynomialRoot16 (d.w0 12925 164) (d.w1 12925 164)
          (d.w2 12925 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12925 : ℝ) ^ 16 *
        (((869556871 / 50000000000000000000) : ℝ) + ((1237346193 / 100000000000000000000)) * (126 / 100) + 2 * ((452094793 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12925) *
          (32 * (((869556871 / 50000000000000000000) : ℝ) + (1237346193 / 100000000000000000000) + (452094793 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12925

/-! A coarse bound on the actual paper statistics constant at dimension 12926. -/
namespace BstLean.Part266.Row12926
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12924 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12924 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12924 128 ≤ (13178 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13178 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12926) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12926 : ℕ))
    (by norm_num : (12926 : ℕ) ≤ 16384)
  have ht : paperTail256 12926 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12926 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12926 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12926 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12926 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12926 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12924 128 * √(2 / (12926 : ℝ)) *
      (√(12926 : ℝ) + paperT0 12926 + paperTail256 12926) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12926 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12926 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12926 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12924 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12924 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12926 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12926

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12926
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12926 (61 / 100) 164 (17 / (100 * 12926)) (26 / (10 * 12926)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12926 (61 / 100) 164 (17 / (100 * 12926)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (225992783 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1398686591 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2219986819 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12926 / 12926 * (61 / 100)) ^ 4 * inverseRadius8 (12926 - 1) /
            envelopeGap 12926 (61 / 100) 164 (17 / (100 * 12926)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12926

namespace BstLean.Part266.Row12926
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12926 164 ≤ (4384996999 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12926 164 ≤ (731454641 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (351610819 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12926 164 ≤ (347741983 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12926 164 ≤ (49482357 / 4000000000000000000)
  w2 : (tableEnvelope C).w2 12926 164 ≤ (451989867 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (225992783 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (225992783 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1398686591 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2219986819 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3626539 / 1000000000) : ℝ) ≤ √(17 / (100 * 12926) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12926) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2125995217 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4674877323 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12926) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12926) ≤ (54704223 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12926) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12926 * (164 : ℝ) ^ 2 + 26 / (10 * 12926) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12926) : ℝ)) (tA 12926 * 164 ^ 2 + 26 / (10 * 12926)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3626539 / 1000000000))) * ((225992783 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3626539 / 1000000000)) ^ 3) * ((1398686591 / 1000000000000000000000000))) + ((2219986819 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3626539 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12926) : ℝ)) d.D d.V d.P (√(tA 12926) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3626539 / 1000000000)) ^ 2 * (((2125995217 / 1000000000000000)) * ((4674877323 / 125000000000000000)))) + ((2219986819 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12926) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3626539 / 1000000000)) * ((225992783 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12926) : ℝ)) (tA 12926 * 164 ^ 2 + 26 / (10 * 12926)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((225992783 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3626539 / 1000000000)) ^ 2) * ((1398686591 / 1000000000000000000000000)) + ((2219986819 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12926) : ℝ)) (√(26 / (10 * 12926) : ℝ)) d.D d.V d.P (√(tA 12926) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3626539 / 1000000000)) * (((2125995217 / 1000000000000000)) * ((4674877323 / 125000000000000000))) + ((2219986819 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12926) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((225992783 / 50000000000000000000) : ℝ) + ((2219986819 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12926

namespace BstLean.Part266.Row12926
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12926 164 ∧
    0 ≤ (tableEnvelope C).f1 12926 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12926 164 ∧
    0 ≤ (tableEnvelope C).w1 12926 164 ∧ 0 ≤ (tableEnvelope C).w2 12926 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12926 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12926 164 ∧ 0 ≤ d.f1 12926 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12926 164 ∧ 0 ≤ d.w1 12926 164 ∧ 0 ≤ d.w2 12926 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12926 ≤ 2 * (228 / 100 : ℝ) / 12926 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12926 ≤ 2 * (370 / 100 : ℝ) / 12926 := by
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
    (completeRAData (tableEnvelope C) 12926 164).locationBound 12926 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12926 164).energyBound 12926 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12926 164) (d.f1 12926 164) d.f2 ≤
      32 * (((4384996999 / 1000000000000000000) : ℝ) + (731454641 / 500000000000000000) + (351610819 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12926 164) (d.w1 12926 164)
      (d.w2 12926 164) ≤
      32 * (((347741983 / 20000000000000000000) : ℝ) + (49482357 / 4000000000000000000) + (451989867 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12926 164) (d.f1 12926 164) d.f2 ≤
      ((4384996999 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4384996999 / 1000000000000000000)) * ((731454641 / 500000000000000000)) * (126 / 100) +
      2 * (((731454641 / 500000000000000000)) ^ 2 + 2 * ((4384996999 / 1000000000000000000)) * ((351610819 / 1000000000000000000))) +
      6 * ((731454641 / 500000000000000000)) * ((351610819 / 1000000000000000000)) * (126 / 100) + 8 * ((351610819 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12926 164) (d.f1 12926 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12926 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12926 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12926 164) (d.f1 12926 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12926 164) (d.w1 12926 164) (d.w2 12926 164)
  have hwexpr0 : 0 ≤ d.w0 12926 164 + d.w1 12926 164 * √(π / 2) +
      2 * d.w2 12926 164 + energyR16 12926 *
      radiusPolynomialRoot16 (d.w0 12926 164) (d.w1 12926 164) (d.w2 12926 164) := by
    positivity
  constructor
  · change (12926 : ℝ) ^ 8 * (mA 12926 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12926 164) (d.f1 12926 164) d.f2 + locationR16 12926 *
        radiusPolynomialRoot16 (d.f0 12926 164) (d.f1 12926 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12926 : ℝ) ^ 8 * (mA 12926 : ℝ) ^ 8 *
        ((((4384996999 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4384996999 / 1000000000000000000)) * ((731454641 / 500000000000000000)) * (126 / 100) +
          2 * (((731454641 / 500000000000000000)) ^ 2 + 2 * ((4384996999 / 1000000000000000000)) * ((351610819 / 1000000000000000000))) +
          6 * ((731454641 / 500000000000000000)) * ((351610819 / 1000000000000000000)) * (126 / 100) + 8 * ((351610819 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12926) *
          (32 * (((4384996999 / 1000000000000000000) : ℝ) + (731454641 / 500000000000000000) + (351610819 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12926 : ℝ) ^ 16 *
      (d.w0 12926 164 + d.w1 12926 164 * √(π / 2) + 2 * d.w2 12926 164 +
        energyR16 12926 * radiusPolynomialRoot16 (d.w0 12926 164) (d.w1 12926 164)
          (d.w2 12926 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12926 : ℝ) ^ 16 *
        (((347741983 / 20000000000000000000) : ℝ) + ((49482357 / 4000000000000000000)) * (126 / 100) + 2 * ((451989867 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12926) *
          (32 * (((347741983 / 20000000000000000000) : ℝ) + (49482357 / 4000000000000000000) + (451989867 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12926

/-! A coarse bound on the actual paper statistics constant at dimension 12927. -/
namespace BstLean.Part266.Row12927
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12925 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12925 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12925 128 ≤ (13179 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13179 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12927) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12927 : ℕ))
    (by norm_num : (12927 : ℕ) ≤ 16384)
  have ht : paperTail256 12927 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12927 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12927 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12927 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12927 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12927 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12925 128 * √(2 / (12927 : ℝ)) *
      (√(12927 : ℝ) + paperT0 12927 + paperTail256 12927) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12927 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12927 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12927 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12925 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12925 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12927 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12927

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12927
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12927 (61 / 100) 164 (17 / (100 * 12927)) (26 / (10 * 12927)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12927 (61 / 100) 164 (17 / (100 * 12927)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (18075227 / 4000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1398253829 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2218600261 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12927 / 12927 * (61 / 100)) ^ 4 * inverseRadius8 (12927 - 1) /
            envelopeGap 12927 (61 / 100) 164 (17 / (100 * 12927)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12927

namespace BstLean.Part266.Row12927
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12927 164 ≤ (4384151503 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12927 164 ≤ (29252539 / 20000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (351542889 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12927 164 ≤ (347661387 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12927 164 ≤ (1236772093 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12927 164 ≤ (225942487 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (18075227 / 4000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (18075227 / 4000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1398253829 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2218600261 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1813199 / 500000000) : ℝ) ≤ √(17 / (100 * 12927) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12927) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (531437129 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9348308099 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12927) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12927) ≤ (54699991 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12927) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12927 * (164 : ℝ) ^ 2 + 26 / (10 * 12927) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12927) : ℝ)) (tA 12927 * 164 ^ 2 + 26 / (10 * 12927)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1813199 / 500000000))) * ((18075227 / 4000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1813199 / 500000000)) ^ 3) * ((1398253829 / 1000000000000000000000000))) + ((2218600261 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1813199 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12927) : ℝ)) d.D d.V d.P (√(tA 12927) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1813199 / 500000000)) ^ 2 * (((531437129 / 250000000000000)) * ((9348308099 / 250000000000000000)))) + ((2218600261 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12927) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1813199 / 500000000)) * ((18075227 / 4000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12927) : ℝ)) (tA 12927 * 164 ^ 2 + 26 / (10 * 12927)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((18075227 / 4000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1813199 / 500000000)) ^ 2) * ((1398253829 / 1000000000000000000000000)) + ((2218600261 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12927) : ℝ)) (√(26 / (10 * 12927) : ℝ)) d.D d.V d.P (√(tA 12927) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1813199 / 500000000)) * (((531437129 / 250000000000000)) * ((9348308099 / 250000000000000000))) + ((2218600261 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12927) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((18075227 / 4000000000000000000) : ℝ) + ((2218600261 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12927

namespace BstLean.Part266.Row12927
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12927 164 ∧
    0 ≤ (tableEnvelope C).f1 12927 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12927 164 ∧
    0 ≤ (tableEnvelope C).w1 12927 164 ∧ 0 ≤ (tableEnvelope C).w2 12927 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12927 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12927 164 ∧ 0 ≤ d.f1 12927 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12927 164 ∧ 0 ≤ d.w1 12927 164 ∧ 0 ≤ d.w2 12927 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12927 ≤ 2 * (228 / 100 : ℝ) / 12927 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12927 ≤ 2 * (370 / 100 : ℝ) / 12927 := by
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
    (completeRAData (tableEnvelope C) 12927 164).locationBound 12927 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12927 164).energyBound 12927 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12927 164) (d.f1 12927 164) d.f2 ≤
      32 * (((4384151503 / 1000000000000000000) : ℝ) + (29252539 / 20000000000000000) + (351542889 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12927 164) (d.w1 12927 164)
      (d.w2 12927 164) ≤
      32 * (((347661387 / 20000000000000000000) : ℝ) + (1236772093 / 100000000000000000000) + (225942487 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12927 164) (d.f1 12927 164) d.f2 ≤
      ((4384151503 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4384151503 / 1000000000000000000)) * ((29252539 / 20000000000000000)) * (126 / 100) +
      2 * (((29252539 / 20000000000000000)) ^ 2 + 2 * ((4384151503 / 1000000000000000000)) * ((351542889 / 1000000000000000000))) +
      6 * ((29252539 / 20000000000000000)) * ((351542889 / 1000000000000000000)) * (126 / 100) + 8 * ((351542889 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12927 164) (d.f1 12927 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12927 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12927 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12927 164) (d.f1 12927 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12927 164) (d.w1 12927 164) (d.w2 12927 164)
  have hwexpr0 : 0 ≤ d.w0 12927 164 + d.w1 12927 164 * √(π / 2) +
      2 * d.w2 12927 164 + energyR16 12927 *
      radiusPolynomialRoot16 (d.w0 12927 164) (d.w1 12927 164) (d.w2 12927 164) := by
    positivity
  constructor
  · change (12927 : ℝ) ^ 8 * (mA 12927 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12927 164) (d.f1 12927 164) d.f2 + locationR16 12927 *
        radiusPolynomialRoot16 (d.f0 12927 164) (d.f1 12927 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12927 : ℝ) ^ 8 * (mA 12927 : ℝ) ^ 8 *
        ((((4384151503 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4384151503 / 1000000000000000000)) * ((29252539 / 20000000000000000)) * (126 / 100) +
          2 * (((29252539 / 20000000000000000)) ^ 2 + 2 * ((4384151503 / 1000000000000000000)) * ((351542889 / 1000000000000000000))) +
          6 * ((29252539 / 20000000000000000)) * ((351542889 / 1000000000000000000)) * (126 / 100) + 8 * ((351542889 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12927) *
          (32 * (((4384151503 / 1000000000000000000) : ℝ) + (29252539 / 20000000000000000) + (351542889 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12927 : ℝ) ^ 16 *
      (d.w0 12927 164 + d.w1 12927 164 * √(π / 2) + 2 * d.w2 12927 164 +
        energyR16 12927 * radiusPolynomialRoot16 (d.w0 12927 164) (d.w1 12927 164)
          (d.w2 12927 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12927 : ℝ) ^ 16 *
        (((347661387 / 20000000000000000000) : ℝ) + ((1236772093 / 100000000000000000000)) * (126 / 100) + 2 * ((225942487 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12927) *
          (32 * (((347661387 / 20000000000000000000) : ℝ) + (1236772093 / 100000000000000000000) + (225942487 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12927

/-! A coarse bound on the actual paper statistics constant at dimension 12928. -/
namespace BstLean.Part266.Row12928
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12926 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12926 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12926 128 ≤ (13180 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13180 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12928) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12928 : ℕ))
    (by norm_num : (12928 : ℕ) ≤ 16384)
  have ht : paperTail256 12928 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12928 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12928 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12928 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12928 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12928 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12926 128 * √(2 / (12928 : ℝ)) *
      (√(12928 : ℝ) + paperT0 12928 + paperTail256 12928) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12928 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12928 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12928 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12926 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12926 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12928 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12928

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12928
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12928 (61 / 100) 164 (17 / (100 * 12928)) (26 / (10 * 12928)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12928 (61 / 100) 164 (17 / (100 * 12928)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (451775817 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (698910617 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4434429357 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12928 / 12928 * (61 / 100)) ^ 4 * inverseRadius8 (12928 - 1) /
            envelopeGap 12928 (61 / 100) 164 (17 / (100 * 12928)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12928

namespace BstLean.Part266.Row12928
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12928 164 ≤ (2191651401 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12928 164 ≤ (1462343901 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (87868721 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12928 164 ≤ (1737903381 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12928 164 ≤ (618242507 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12928 164 ≤ (451780113 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (451775817 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (451775817 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (698910617 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4434429357 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1813129 / 500000000) : ℝ) ≤ √(17 / (100 * 12928) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12928) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (265687733 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18693723773 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12928) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12928) ≤ (683697 / 6250000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12928) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12928 * (164 : ℝ) ^ 2 + 26 / (10 * 12928) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12928) : ℝ)) (tA 12928 * 164 ^ 2 + 26 / (10 * 12928)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1813129 / 500000000))) * ((451775817 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1813129 / 500000000)) ^ 3) * ((698910617 / 500000000000000000000000))) + ((4434429357 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1813129 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12928) : ℝ)) d.D d.V d.P (√(tA 12928) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1813129 / 500000000)) ^ 2 * (((265687733 / 125000000000000)) * ((18693723773 / 500000000000000000)))) + ((4434429357 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12928) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1813129 / 500000000)) * ((451775817 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12928) : ℝ)) (tA 12928 * 164 ^ 2 + 26 / (10 * 12928)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((451775817 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1813129 / 500000000)) ^ 2) * ((698910617 / 500000000000000000000000)) + ((4434429357 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12928) : ℝ)) (√(26 / (10 * 12928) : ℝ)) d.D d.V d.P (√(tA 12928) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1813129 / 500000000)) * (((265687733 / 125000000000000)) * ((18693723773 / 500000000000000000))) + ((4434429357 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12928) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((451775817 / 100000000000000000000) : ℝ) + ((4434429357 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12928

namespace BstLean.Part266.Row12928
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12928 164 ∧
    0 ≤ (tableEnvelope C).f1 12928 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12928 164 ∧
    0 ≤ (tableEnvelope C).w1 12928 164 ∧ 0 ≤ (tableEnvelope C).w2 12928 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12928 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12928 164 ∧ 0 ≤ d.f1 12928 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12928 164 ∧ 0 ≤ d.w1 12928 164 ∧ 0 ≤ d.w2 12928 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12928 ≤ 2 * (228 / 100 : ℝ) / 12928 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12928 ≤ 2 * (370 / 100 : ℝ) / 12928 := by
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
    (completeRAData (tableEnvelope C) 12928 164).locationBound 12928 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12928 164).energyBound 12928 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12928 164) (d.f1 12928 164) d.f2 ≤
      32 * (((2191651401 / 500000000000000000) : ℝ) + (1462343901 / 1000000000000000000) + (87868721 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12928 164) (d.w1 12928 164)
      (d.w2 12928 164) ≤
      32 * (((1737903381 / 100000000000000000000) : ℝ) + (618242507 / 50000000000000000000) + (451780113 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12928 164) (d.f1 12928 164) d.f2 ≤
      ((2191651401 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2191651401 / 500000000000000000)) * ((1462343901 / 1000000000000000000)) * (126 / 100) +
      2 * (((1462343901 / 1000000000000000000)) ^ 2 + 2 * ((2191651401 / 500000000000000000)) * ((87868721 / 250000000000000000))) +
      6 * ((1462343901 / 1000000000000000000)) * ((87868721 / 250000000000000000)) * (126 / 100) + 8 * ((87868721 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12928 164) (d.f1 12928 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12928 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12928 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12928 164) (d.f1 12928 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12928 164) (d.w1 12928 164) (d.w2 12928 164)
  have hwexpr0 : 0 ≤ d.w0 12928 164 + d.w1 12928 164 * √(π / 2) +
      2 * d.w2 12928 164 + energyR16 12928 *
      radiusPolynomialRoot16 (d.w0 12928 164) (d.w1 12928 164) (d.w2 12928 164) := by
    positivity
  constructor
  · change (12928 : ℝ) ^ 8 * (mA 12928 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12928 164) (d.f1 12928 164) d.f2 + locationR16 12928 *
        radiusPolynomialRoot16 (d.f0 12928 164) (d.f1 12928 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12928 : ℝ) ^ 8 * (mA 12928 : ℝ) ^ 8 *
        ((((2191651401 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2191651401 / 500000000000000000)) * ((1462343901 / 1000000000000000000)) * (126 / 100) +
          2 * (((1462343901 / 1000000000000000000)) ^ 2 + 2 * ((2191651401 / 500000000000000000)) * ((87868721 / 250000000000000000))) +
          6 * ((1462343901 / 1000000000000000000)) * ((87868721 / 250000000000000000)) * (126 / 100) + 8 * ((87868721 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12928) *
          (32 * (((2191651401 / 500000000000000000) : ℝ) + (1462343901 / 1000000000000000000) + (87868721 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12928 : ℝ) ^ 16 *
      (d.w0 12928 164 + d.w1 12928 164 * √(π / 2) + 2 * d.w2 12928 164 +
        energyR16 12928 * radiusPolynomialRoot16 (d.w0 12928 164) (d.w1 12928 164)
          (d.w2 12928 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12928 : ℝ) ^ 16 *
        (((1737903381 / 100000000000000000000) : ℝ) + ((618242507 / 50000000000000000000)) * (126 / 100) + 2 * ((451780113 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12928) *
          (32 * (((1737903381 / 100000000000000000000) : ℝ) + (618242507 / 50000000000000000000) + (451780113 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12928

/-! A coarse bound on the actual paper statistics constant at dimension 12929. -/
namespace BstLean.Part266.Row12929
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12927 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12927 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12927 128 ≤ (13181 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13181 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12929) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12929 : ℕ))
    (by norm_num : (12929 : ℕ) ≤ 16384)
  have ht : paperTail256 12929 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12929 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12929 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12929 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12929 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12929 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12927 128 * √(2 / (12929 : ℝ)) *
      (√(12929 : ℝ) + paperT0 12929 + paperTail256 12929) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12929 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12929 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12929 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12927 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12927 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12929 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12929

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12929
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12929 (61 / 100) 164 (17 / (100 * 12929)) (26 / (10 * 12929)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12929 (61 / 100) 164 (17 / (100 * 12929)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (451670991 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1397388807 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (221583007 / 50000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12929 / 12929 * (61 / 100)) ^ 4 * inverseRadius8 (12929 - 1) /
            envelopeGap 12929 (61 / 100) 164 (17 / (100 * 12929)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12929

namespace BstLean.Part266.Row12929
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12929 164 ≤ (438245439 / 100000000000000000)
  f1 : (tableEnvelope C).f1 12929 164 ≤ (1462060941 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (351406897 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12929 164 ≤ (1737499963 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12929 164 ≤ (1236198029 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12929 164 ≤ (112918821 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (451670991 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (451670991 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1397388807 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (221583007 / 50000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1813059 / 500000000) : ℝ) ≤ √(17 / (100 * 12929) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12929) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1062627629 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37381664049 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12929) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12929) ≤ (109383059 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12929) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12929 * (164 : ℝ) ^ 2 + 26 / (10 * 12929) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12929) : ℝ)) (tA 12929 * 164 ^ 2 + 26 / (10 * 12929)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1813059 / 500000000))) * ((451670991 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1813059 / 500000000)) ^ 3) * ((1397388807 / 1000000000000000000000000))) + ((221583007 / 50000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1813059 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12929) : ℝ)) d.D d.V d.P (√(tA 12929) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1813059 / 500000000)) ^ 2 * (((1062627629 / 500000000000000)) * ((37381664049 / 1000000000000000000)))) + ((221583007 / 50000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12929) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1813059 / 500000000)) * ((451670991 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12929) : ℝ)) (tA 12929 * 164 ^ 2 + 26 / (10 * 12929)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((451670991 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1813059 / 500000000)) ^ 2) * ((1397388807 / 1000000000000000000000000)) + ((221583007 / 50000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12929) : ℝ)) (√(26 / (10 * 12929) : ℝ)) d.D d.V d.P (√(tA 12929) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1813059 / 500000000)) * (((1062627629 / 500000000000000)) * ((37381664049 / 1000000000000000000))) + ((221583007 / 50000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12929) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((451670991 / 100000000000000000000) : ℝ) + ((221583007 / 50000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12929

namespace BstLean.Part266.Row12929
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12929 164 ∧
    0 ≤ (tableEnvelope C).f1 12929 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12929 164 ∧
    0 ≤ (tableEnvelope C).w1 12929 164 ∧ 0 ≤ (tableEnvelope C).w2 12929 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12929 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12929 164 ∧ 0 ≤ d.f1 12929 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12929 164 ∧ 0 ≤ d.w1 12929 164 ∧ 0 ≤ d.w2 12929 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12929 ≤ 2 * (228 / 100 : ℝ) / 12929 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12929 ≤ 2 * (370 / 100 : ℝ) / 12929 := by
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
    (completeRAData (tableEnvelope C) 12929 164).locationBound 12929 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12929 164).energyBound 12929 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12929 164) (d.f1 12929 164) d.f2 ≤
      32 * (((438245439 / 100000000000000000) : ℝ) + (1462060941 / 1000000000000000000) + (351406897 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12929 164) (d.w1 12929 164)
      (d.w2 12929 164) ≤
      32 * (((1737499963 / 100000000000000000000) : ℝ) + (1236198029 / 100000000000000000000) + (112918821 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12929 164) (d.f1 12929 164) d.f2 ≤
      ((438245439 / 100000000000000000) : ℝ) ^ 2 + 2 * ((438245439 / 100000000000000000)) * ((1462060941 / 1000000000000000000)) * (126 / 100) +
      2 * (((1462060941 / 1000000000000000000)) ^ 2 + 2 * ((438245439 / 100000000000000000)) * ((351406897 / 1000000000000000000))) +
      6 * ((1462060941 / 1000000000000000000)) * ((351406897 / 1000000000000000000)) * (126 / 100) + 8 * ((351406897 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12929 164) (d.f1 12929 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12929 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12929 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12929 164) (d.f1 12929 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12929 164) (d.w1 12929 164) (d.w2 12929 164)
  have hwexpr0 : 0 ≤ d.w0 12929 164 + d.w1 12929 164 * √(π / 2) +
      2 * d.w2 12929 164 + energyR16 12929 *
      radiusPolynomialRoot16 (d.w0 12929 164) (d.w1 12929 164) (d.w2 12929 164) := by
    positivity
  constructor
  · change (12929 : ℝ) ^ 8 * (mA 12929 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12929 164) (d.f1 12929 164) d.f2 + locationR16 12929 *
        radiusPolynomialRoot16 (d.f0 12929 164) (d.f1 12929 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12929 : ℝ) ^ 8 * (mA 12929 : ℝ) ^ 8 *
        ((((438245439 / 100000000000000000) : ℝ) ^ 2 + 2 * ((438245439 / 100000000000000000)) * ((1462060941 / 1000000000000000000)) * (126 / 100) +
          2 * (((1462060941 / 1000000000000000000)) ^ 2 + 2 * ((438245439 / 100000000000000000)) * ((351406897 / 1000000000000000000))) +
          6 * ((1462060941 / 1000000000000000000)) * ((351406897 / 1000000000000000000)) * (126 / 100) + 8 * ((351406897 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12929) *
          (32 * (((438245439 / 100000000000000000) : ℝ) + (1462060941 / 1000000000000000000) + (351406897 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12929 : ℝ) ^ 16 *
      (d.w0 12929 164 + d.w1 12929 164 * √(π / 2) + 2 * d.w2 12929 164 +
        energyR16 12929 * radiusPolynomialRoot16 (d.w0 12929 164) (d.w1 12929 164)
          (d.w2 12929 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12929 : ℝ) ^ 16 *
        (((1737499963 / 100000000000000000000) : ℝ) + ((1236198029 / 100000000000000000000)) * (126 / 100) + 2 * ((112918821 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12929) *
          (32 * (((1737499963 / 100000000000000000000) : ℝ) + (1236198029 / 100000000000000000000) + (112918821 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12929

/-! A coarse bound on the actual paper statistics constant at dimension 12930. -/
namespace BstLean.Part266.Row12930
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12928 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12928 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12928 128 ≤ (13182 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13182 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12930) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12930 : ℕ))
    (by norm_num : (12930 : ℕ) ≤ 16384)
  have ht : paperTail256 12930 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12930 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12930 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12930 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12930 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12930 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12928 128 * √(2 / (12930 : ℝ)) *
      (√(12930 : ℝ) + paperT0 12930 + paperTail256 12930) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12930 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12930 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12930 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12928 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12928 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12930 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12930

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12930
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12930 (61 / 100) 164 (17 / (100 * 12930)) (26 / (10 * 12930)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12930 (61 / 100) 164 (17 / (100 * 12930)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (225783099 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1396956547 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (442889287 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12930 / 12930 * (61 / 100)) ^ 4 * inverseRadius8 (12930 - 1) /
            envelopeGap 12930 (61 / 100) 164 (17 / (100 * 12930)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12930

namespace BstLean.Part266.Row12930
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12930 164 ≤ (547700783 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12930 164 ≤ (1461778073 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (87834733 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12930 164 ≤ (1737096683 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12930 164 ≤ (61795557 / 5000000000000000000)
  w2 : (tableEnvelope C).w2 12930 164 ≤ (451570489 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (225783099 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (225783099 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1396956547 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (442889287 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1812989 / 500000000) : ℝ) ≤ √(17 / (100 * 12930) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12930) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1062504351 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3737588189 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12930) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12930) ≤ (109374599 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12930) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12930 * (164 : ℝ) ^ 2 + 26 / (10 * 12930) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12930) : ℝ)) (tA 12930 * 164 ^ 2 + 26 / (10 * 12930)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1812989 / 500000000))) * ((225783099 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1812989 / 500000000)) ^ 3) * ((1396956547 / 1000000000000000000000000))) + ((442889287 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1812989 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12930) : ℝ)) d.D d.V d.P (√(tA 12930) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1812989 / 500000000)) ^ 2 * (((1062504351 / 500000000000000)) * ((3737588189 / 100000000000000000)))) + ((442889287 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12930) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1812989 / 500000000)) * ((225783099 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12930) : ℝ)) (tA 12930 * 164 ^ 2 + 26 / (10 * 12930)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((225783099 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1812989 / 500000000)) ^ 2) * ((1396956547 / 1000000000000000000000000)) + ((442889287 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12930) : ℝ)) (√(26 / (10 * 12930) : ℝ)) d.D d.V d.P (√(tA 12930) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1812989 / 500000000)) * (((1062504351 / 500000000000000)) * ((3737588189 / 100000000000000000))) + ((442889287 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12930) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((225783099 / 50000000000000000000) : ℝ) + ((442889287 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12930

namespace BstLean.Part266.Row12930
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12930 164 ∧
    0 ≤ (tableEnvelope C).f1 12930 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12930 164 ∧
    0 ≤ (tableEnvelope C).w1 12930 164 ∧ 0 ≤ (tableEnvelope C).w2 12930 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12930 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12930 164 ∧ 0 ≤ d.f1 12930 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12930 164 ∧ 0 ≤ d.w1 12930 164 ∧ 0 ≤ d.w2 12930 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12930 ≤ 2 * (228 / 100 : ℝ) / 12930 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12930 ≤ 2 * (370 / 100 : ℝ) / 12930 := by
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
    (completeRAData (tableEnvelope C) 12930 164).locationBound 12930 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12930 164).energyBound 12930 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12930 164) (d.f1 12930 164) d.f2 ≤
      32 * (((547700783 / 125000000000000000) : ℝ) + (1461778073 / 1000000000000000000) + (87834733 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12930 164) (d.w1 12930 164)
      (d.w2 12930 164) ≤
      32 * (((1737096683 / 100000000000000000000) : ℝ) + (61795557 / 5000000000000000000) + (451570489 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12930 164) (d.f1 12930 164) d.f2 ≤
      ((547700783 / 125000000000000000) : ℝ) ^ 2 + 2 * ((547700783 / 125000000000000000)) * ((1461778073 / 1000000000000000000)) * (126 / 100) +
      2 * (((1461778073 / 1000000000000000000)) ^ 2 + 2 * ((547700783 / 125000000000000000)) * ((87834733 / 250000000000000000))) +
      6 * ((1461778073 / 1000000000000000000)) * ((87834733 / 250000000000000000)) * (126 / 100) + 8 * ((87834733 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12930 164) (d.f1 12930 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12930 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12930 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12930 164) (d.f1 12930 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12930 164) (d.w1 12930 164) (d.w2 12930 164)
  have hwexpr0 : 0 ≤ d.w0 12930 164 + d.w1 12930 164 * √(π / 2) +
      2 * d.w2 12930 164 + energyR16 12930 *
      radiusPolynomialRoot16 (d.w0 12930 164) (d.w1 12930 164) (d.w2 12930 164) := by
    positivity
  constructor
  · change (12930 : ℝ) ^ 8 * (mA 12930 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12930 164) (d.f1 12930 164) d.f2 + locationR16 12930 *
        radiusPolynomialRoot16 (d.f0 12930 164) (d.f1 12930 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12930 : ℝ) ^ 8 * (mA 12930 : ℝ) ^ 8 *
        ((((547700783 / 125000000000000000) : ℝ) ^ 2 + 2 * ((547700783 / 125000000000000000)) * ((1461778073 / 1000000000000000000)) * (126 / 100) +
          2 * (((1461778073 / 1000000000000000000)) ^ 2 + 2 * ((547700783 / 125000000000000000)) * ((87834733 / 250000000000000000))) +
          6 * ((1461778073 / 1000000000000000000)) * ((87834733 / 250000000000000000)) * (126 / 100) + 8 * ((87834733 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12930) *
          (32 * (((547700783 / 125000000000000000) : ℝ) + (1461778073 / 1000000000000000000) + (87834733 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12930 : ℝ) ^ 16 *
      (d.w0 12930 164 + d.w1 12930 164 * √(π / 2) + 2 * d.w2 12930 164 +
        energyR16 12930 * radiusPolynomialRoot16 (d.w0 12930 164) (d.w1 12930 164)
          (d.w2 12930 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12930 : ℝ) ^ 16 *
        (((1737096683 / 100000000000000000000) : ℝ) + ((61795557 / 5000000000000000000)) * (126 / 100) + 2 * ((451570489 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12930) *
          (32 * (((1737096683 / 100000000000000000000) : ℝ) + (61795557 / 5000000000000000000) + (451570489 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12930

/-! A coarse bound on the actual paper statistics constant at dimension 12931. -/
namespace BstLean.Part266.Row12931
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12929 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12929 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12929 128 ≤ (13183 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13183 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12931) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12931 : ℕ))
    (by norm_num : (12931 : ℕ) ≤ 16384)
  have ht : paperTail256 12931 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12931 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12931 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12931 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12931 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12931 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12929 128 * √(2 / (12931 : ℝ)) *
      (√(12931 : ℝ) + paperT0 12931 + paperTail256 12931) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12931 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12931 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12931 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12929 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12929 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12931 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12931

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12931
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12931 (61 / 100) 164 (17 / (100 * 12931)) (26 / (10 * 12931)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12931 (61 / 100) 164 (17 / (100 * 12931)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (451461437 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (698262227 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4426127547 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12931 / 12931 * (61 / 100)) ^ 4 * inverseRadius8 (12931 - 1) /
            envelopeGap 12931 (61 / 100) 164 (17 / (100 * 12931)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12931

namespace BstLean.Part266.Row12931
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12931 164 ≤ (547594803 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12931 164 ≤ (1461495293 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (70254197 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12931 164 ≤ (868346769 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12931 164 ≤ (154453043 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 12931 164 ≤ (18058629 / 4000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (451461437 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (451461437 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (698262227 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4426127547 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1812919 / 500000000) : ℝ) ≤ √(17 / (100 * 12931) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12931) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (132797637 / 62500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37370101071 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12931) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12931) ≤ (109366141 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12931) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12931 * (164 : ℝ) ^ 2 + 26 / (10 * 12931) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12931) : ℝ)) (tA 12931 * 164 ^ 2 + 26 / (10 * 12931)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1812919 / 500000000))) * ((451461437 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1812919 / 500000000)) ^ 3) * ((698262227 / 500000000000000000000000))) + ((4426127547 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1812919 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12931) : ℝ)) d.D d.V d.P (√(tA 12931) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1812919 / 500000000)) ^ 2 * (((132797637 / 62500000000000)) * ((37370101071 / 1000000000000000000)))) + ((4426127547 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12931) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1812919 / 500000000)) * ((451461437 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12931) : ℝ)) (tA 12931 * 164 ^ 2 + 26 / (10 * 12931)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((451461437 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1812919 / 500000000)) ^ 2) * ((698262227 / 500000000000000000000000)) + ((4426127547 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12931) : ℝ)) (√(26 / (10 * 12931) : ℝ)) d.D d.V d.P (√(tA 12931) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1812919 / 500000000)) * (((132797637 / 62500000000000)) * ((37370101071 / 1000000000000000000))) + ((4426127547 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12931) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((451461437 / 100000000000000000000) : ℝ) + ((4426127547 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12931

namespace BstLean.Part266.Row12931
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12931 164 ∧
    0 ≤ (tableEnvelope C).f1 12931 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12931 164 ∧
    0 ≤ (tableEnvelope C).w1 12931 164 ∧ 0 ≤ (tableEnvelope C).w2 12931 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12931 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12931 164 ∧ 0 ≤ d.f1 12931 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12931 164 ∧ 0 ≤ d.w1 12931 164 ∧ 0 ≤ d.w2 12931 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12931 ≤ 2 * (228 / 100 : ℝ) / 12931 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12931 ≤ 2 * (370 / 100 : ℝ) / 12931 := by
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
    (completeRAData (tableEnvelope C) 12931 164).locationBound 12931 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12931 164).energyBound 12931 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12931 164) (d.f1 12931 164) d.f2 ≤
      32 * (((547594803 / 125000000000000000) : ℝ) + (1461495293 / 1000000000000000000) + (70254197 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12931 164) (d.w1 12931 164)
      (d.w2 12931 164) ≤
      32 * (((868346769 / 50000000000000000000) : ℝ) + (154453043 / 12500000000000000000) + (18058629 / 4000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12931 164) (d.f1 12931 164) d.f2 ≤
      ((547594803 / 125000000000000000) : ℝ) ^ 2 + 2 * ((547594803 / 125000000000000000)) * ((1461495293 / 1000000000000000000)) * (126 / 100) +
      2 * (((1461495293 / 1000000000000000000)) ^ 2 + 2 * ((547594803 / 125000000000000000)) * ((70254197 / 200000000000000000))) +
      6 * ((1461495293 / 1000000000000000000)) * ((70254197 / 200000000000000000)) * (126 / 100) + 8 * ((70254197 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12931 164) (d.f1 12931 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12931 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12931 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12931 164) (d.f1 12931 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12931 164) (d.w1 12931 164) (d.w2 12931 164)
  have hwexpr0 : 0 ≤ d.w0 12931 164 + d.w1 12931 164 * √(π / 2) +
      2 * d.w2 12931 164 + energyR16 12931 *
      radiusPolynomialRoot16 (d.w0 12931 164) (d.w1 12931 164) (d.w2 12931 164) := by
    positivity
  constructor
  · change (12931 : ℝ) ^ 8 * (mA 12931 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12931 164) (d.f1 12931 164) d.f2 + locationR16 12931 *
        radiusPolynomialRoot16 (d.f0 12931 164) (d.f1 12931 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12931 : ℝ) ^ 8 * (mA 12931 : ℝ) ^ 8 *
        ((((547594803 / 125000000000000000) : ℝ) ^ 2 + 2 * ((547594803 / 125000000000000000)) * ((1461495293 / 1000000000000000000)) * (126 / 100) +
          2 * (((1461495293 / 1000000000000000000)) ^ 2 + 2 * ((547594803 / 125000000000000000)) * ((70254197 / 200000000000000000))) +
          6 * ((1461495293 / 1000000000000000000)) * ((70254197 / 200000000000000000)) * (126 / 100) + 8 * ((70254197 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12931) *
          (32 * (((547594803 / 125000000000000000) : ℝ) + (1461495293 / 1000000000000000000) + (70254197 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12931 : ℝ) ^ 16 *
      (d.w0 12931 164 + d.w1 12931 164 * √(π / 2) + 2 * d.w2 12931 164 +
        energyR16 12931 * radiusPolynomialRoot16 (d.w0 12931 164) (d.w1 12931 164)
          (d.w2 12931 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12931 : ℝ) ^ 16 *
        (((868346769 / 50000000000000000000) : ℝ) + ((154453043 / 12500000000000000000)) * (126 / 100) + 2 * ((18058629 / 4000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12931) *
          (32 * (((868346769 / 50000000000000000000) : ℝ) + (154453043 / 12500000000000000000) + (18058629 / 4000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12931

/-! A coarse bound on the actual paper statistics constant at dimension 12932. -/
namespace BstLean.Part266.Row12932
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12930 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12930 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12930 128 ≤ (13184 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13184 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12932) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12932 : ℕ))
    (by norm_num : (12932 : ℕ) ≤ 16384)
  have ht : paperTail256 12932 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12932 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12932 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12932 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12932 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12932 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12930 128 * √(2 / (12932 : ℝ)) *
      (√(12932 : ℝ) + paperT0 12932 + paperTail256 12932) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12932 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12932 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12932 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12930 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12930 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12932 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12932

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12932
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12932 (61 / 100) 164 (17 / (100 * 12932)) (26 / (10 * 12932)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12932 (61 / 100) 164 (17 / (100 * 12932)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (112839177 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (87255783 / 62500000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4423364167 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12932 / 12932 * (61 / 100)) ^ 4 * inverseRadius8 (12932 - 1) /
            envelopeGap 12932 (61 / 100) 164 (17 / (100 * 12932)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12932

namespace BstLean.Part266.Row12932
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12932 164 ≤ (1094978589 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12932 164 ≤ (45662919 / 31250000000000000)
  f2 : (tableEnvelope C).f2 ≤ (87800789 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12932 164 ≤ (868145619 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12932 164 ≤ (1235337983 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12932 164 ≤ (451360993 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (112839177 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (112839177 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (87255783 / 62500000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4423364167 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3625697 / 1000000000) : ℝ) ≤ √(17 / (100 * 12932) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12932) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2124515729 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4670540199 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12932) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12932) ≤ (27339421 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12932) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12932 * (164 : ℝ) ^ 2 + 26 / (10 * 12932) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12932) : ℝ)) (tA 12932 * 164 ^ 2 + 26 / (10 * 12932)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3625697 / 1000000000))) * ((112839177 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3625697 / 1000000000)) ^ 3) * ((87255783 / 62500000000000000000000))) + ((4423364167 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3625697 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12932) : ℝ)) d.D d.V d.P (√(tA 12932) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3625697 / 1000000000)) ^ 2 * (((2124515729 / 1000000000000000)) * ((4670540199 / 125000000000000000)))) + ((4423364167 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12932) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3625697 / 1000000000)) * ((112839177 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12932) : ℝ)) (tA 12932 * 164 ^ 2 + 26 / (10 * 12932)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((112839177 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3625697 / 1000000000)) ^ 2) * ((87255783 / 62500000000000000000000)) + ((4423364167 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12932) : ℝ)) (√(26 / (10 * 12932) : ℝ)) d.D d.V d.P (√(tA 12932) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3625697 / 1000000000)) * (((2124515729 / 1000000000000000)) * ((4670540199 / 125000000000000000))) + ((4423364167 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12932) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((112839177 / 25000000000000000000) : ℝ) + ((4423364167 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12932

namespace BstLean.Part266.Row12932
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12932 164 ∧
    0 ≤ (tableEnvelope C).f1 12932 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12932 164 ∧
    0 ≤ (tableEnvelope C).w1 12932 164 ∧ 0 ≤ (tableEnvelope C).w2 12932 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12932 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12932 164 ∧ 0 ≤ d.f1 12932 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12932 164 ∧ 0 ≤ d.w1 12932 164 ∧ 0 ≤ d.w2 12932 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12932 ≤ 2 * (228 / 100 : ℝ) / 12932 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12932 ≤ 2 * (370 / 100 : ℝ) / 12932 := by
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
    (completeRAData (tableEnvelope C) 12932 164).locationBound 12932 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12932 164).energyBound 12932 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12932 164) (d.f1 12932 164) d.f2 ≤
      32 * (((1094978589 / 250000000000000000) : ℝ) + (45662919 / 31250000000000000) + (87800789 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12932 164) (d.w1 12932 164)
      (d.w2 12932 164) ≤
      32 * (((868145619 / 50000000000000000000) : ℝ) + (1235337983 / 100000000000000000000) + (451360993 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12932 164) (d.f1 12932 164) d.f2 ≤
      ((1094978589 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1094978589 / 250000000000000000)) * ((45662919 / 31250000000000000)) * (126 / 100) +
      2 * (((45662919 / 31250000000000000)) ^ 2 + 2 * ((1094978589 / 250000000000000000)) * ((87800789 / 250000000000000000))) +
      6 * ((45662919 / 31250000000000000)) * ((87800789 / 250000000000000000)) * (126 / 100) + 8 * ((87800789 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12932 164) (d.f1 12932 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12932 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12932 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12932 164) (d.f1 12932 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12932 164) (d.w1 12932 164) (d.w2 12932 164)
  have hwexpr0 : 0 ≤ d.w0 12932 164 + d.w1 12932 164 * √(π / 2) +
      2 * d.w2 12932 164 + energyR16 12932 *
      radiusPolynomialRoot16 (d.w0 12932 164) (d.w1 12932 164) (d.w2 12932 164) := by
    positivity
  constructor
  · change (12932 : ℝ) ^ 8 * (mA 12932 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12932 164) (d.f1 12932 164) d.f2 + locationR16 12932 *
        radiusPolynomialRoot16 (d.f0 12932 164) (d.f1 12932 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12932 : ℝ) ^ 8 * (mA 12932 : ℝ) ^ 8 *
        ((((1094978589 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1094978589 / 250000000000000000)) * ((45662919 / 31250000000000000)) * (126 / 100) +
          2 * (((45662919 / 31250000000000000)) ^ 2 + 2 * ((1094978589 / 250000000000000000)) * ((87800789 / 250000000000000000))) +
          6 * ((45662919 / 31250000000000000)) * ((87800789 / 250000000000000000)) * (126 / 100) + 8 * ((87800789 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12932) *
          (32 * (((1094978589 / 250000000000000000) : ℝ) + (45662919 / 31250000000000000) + (87800789 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12932 : ℝ) ^ 16 *
      (d.w0 12932 164 + d.w1 12932 164 * √(π / 2) + 2 * d.w2 12932 164 +
        energyR16 12932 * radiusPolynomialRoot16 (d.w0 12932 164) (d.w1 12932 164)
          (d.w2 12932 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12932 : ℝ) ^ 16 *
        (((868145619 / 50000000000000000000) : ℝ) + ((1235337983 / 100000000000000000000)) * (126 / 100) + 2 * ((451360993 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12932) *
          (32 * (((868145619 / 50000000000000000000) : ℝ) + (1235337983 / 100000000000000000000) + (451360993 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12932

/-! A coarse bound on the actual paper statistics constant at dimension 12933. -/
namespace BstLean.Part266.Row12933
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12931 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12931 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12931 128 ≤ (13185 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13185 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12933) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12933 : ℕ))
    (by norm_num : (12933 : ℕ) ≤ 16384)
  have ht : paperTail256 12933 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12933 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12933 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12933 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12933 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12933 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12931 128 * √(2 / (12933 : ℝ)) *
      (√(12933 : ℝ) + paperT0 12933 + paperTail256 12933) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12933 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12933 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12933 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12931 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12931 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12933 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12933

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12933
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12933 (61 / 100) 164 (17 / (100 * 12933)) (26 / (10 * 12933)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12933 (61 / 100) 164 (17 / (100 * 12933)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (112813003 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1395660769 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4420602731 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12933 / 12933 * (61 / 100)) ^ 4 * inverseRadius8 (12933 - 1) /
            envelopeGap 12933 (61 / 100) 164 (17 / (100 * 12933)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12933

namespace BstLean.Part266.Row12933
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12933 164 ≤ (273691693 / 62500000000000000)
  f1 : (tableEnvelope C).f1 12933 164 ≤ (1460930807 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (1404541 / 4000000000000000)
  w0 : (tableEnvelope C).w0 12933 164 ≤ (867944183 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12933 164 ≤ (9880411 / 800000000000000000)
  w2 : (tableEnvelope C).w2 12933 164 ≤ (90251259 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (112813003 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (112813003 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1395660769 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4420602731 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3625557 / 1000000000) : ℝ) ≤ √(17 / (100 * 12933) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12933) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (424853863 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18679271727 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12933) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12933) ≤ (27337307 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12933) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12933 * (164 : ℝ) ^ 2 + 26 / (10 * 12933) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12933) : ℝ)) (tA 12933 * 164 ^ 2 + 26 / (10 * 12933)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3625557 / 1000000000))) * ((112813003 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3625557 / 1000000000)) ^ 3) * ((1395660769 / 1000000000000000000000000))) + ((4420602731 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3625557 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12933) : ℝ)) d.D d.V d.P (√(tA 12933) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3625557 / 1000000000)) ^ 2 * (((424853863 / 200000000000000)) * ((18679271727 / 500000000000000000)))) + ((4420602731 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12933) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3625557 / 1000000000)) * ((112813003 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12933) : ℝ)) (tA 12933 * 164 ^ 2 + 26 / (10 * 12933)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((112813003 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3625557 / 1000000000)) ^ 2) * ((1395660769 / 1000000000000000000000000)) + ((4420602731 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12933) : ℝ)) (√(26 / (10 * 12933) : ℝ)) d.D d.V d.P (√(tA 12933) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3625557 / 1000000000)) * (((424853863 / 200000000000000)) * ((18679271727 / 500000000000000000))) + ((4420602731 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12933) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((112813003 / 25000000000000000000) : ℝ) + ((4420602731 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12933

namespace BstLean.Part266.Row12933
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12933 164 ∧
    0 ≤ (tableEnvelope C).f1 12933 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12933 164 ∧
    0 ≤ (tableEnvelope C).w1 12933 164 ∧ 0 ≤ (tableEnvelope C).w2 12933 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12933 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12933 164 ∧ 0 ≤ d.f1 12933 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12933 164 ∧ 0 ≤ d.w1 12933 164 ∧ 0 ≤ d.w2 12933 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12933 ≤ 2 * (228 / 100 : ℝ) / 12933 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12933 ≤ 2 * (370 / 100 : ℝ) / 12933 := by
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
    (completeRAData (tableEnvelope C) 12933 164).locationBound 12933 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12933 164).energyBound 12933 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12933 164) (d.f1 12933 164) d.f2 ≤
      32 * (((273691693 / 62500000000000000) : ℝ) + (1460930807 / 1000000000000000000) + (1404541 / 4000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12933 164) (d.w1 12933 164)
      (d.w2 12933 164) ≤
      32 * (((867944183 / 50000000000000000000) : ℝ) + (9880411 / 800000000000000000) + (90251259 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12933 164) (d.f1 12933 164) d.f2 ≤
      ((273691693 / 62500000000000000) : ℝ) ^ 2 + 2 * ((273691693 / 62500000000000000)) * ((1460930807 / 1000000000000000000)) * (126 / 100) +
      2 * (((1460930807 / 1000000000000000000)) ^ 2 + 2 * ((273691693 / 62500000000000000)) * ((1404541 / 4000000000000000))) +
      6 * ((1460930807 / 1000000000000000000)) * ((1404541 / 4000000000000000)) * (126 / 100) + 8 * ((1404541 / 4000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12933 164) (d.f1 12933 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12933 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12933 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12933 164) (d.f1 12933 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12933 164) (d.w1 12933 164) (d.w2 12933 164)
  have hwexpr0 : 0 ≤ d.w0 12933 164 + d.w1 12933 164 * √(π / 2) +
      2 * d.w2 12933 164 + energyR16 12933 *
      radiusPolynomialRoot16 (d.w0 12933 164) (d.w1 12933 164) (d.w2 12933 164) := by
    positivity
  constructor
  · change (12933 : ℝ) ^ 8 * (mA 12933 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12933 164) (d.f1 12933 164) d.f2 + locationR16 12933 *
        radiusPolynomialRoot16 (d.f0 12933 164) (d.f1 12933 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12933 : ℝ) ^ 8 * (mA 12933 : ℝ) ^ 8 *
        ((((273691693 / 62500000000000000) : ℝ) ^ 2 + 2 * ((273691693 / 62500000000000000)) * ((1460930807 / 1000000000000000000)) * (126 / 100) +
          2 * (((1460930807 / 1000000000000000000)) ^ 2 + 2 * ((273691693 / 62500000000000000)) * ((1404541 / 4000000000000000))) +
          6 * ((1460930807 / 1000000000000000000)) * ((1404541 / 4000000000000000)) * (126 / 100) + 8 * ((1404541 / 4000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12933) *
          (32 * (((273691693 / 62500000000000000) : ℝ) + (1460930807 / 1000000000000000000) + (1404541 / 4000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12933 : ℝ) ^ 16 *
      (d.w0 12933 164 + d.w1 12933 164 * √(π / 2) + 2 * d.w2 12933 164 +
        energyR16 12933 * radiusPolynomialRoot16 (d.w0 12933 164) (d.w1 12933 164)
          (d.w2 12933 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12933 : ℝ) ^ 16 *
        (((867944183 / 50000000000000000000) : ℝ) + ((9880411 / 800000000000000000)) * (126 / 100) + 2 * ((90251259 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12933) *
          (32 * (((867944183 / 50000000000000000000) : ℝ) + (9880411 / 800000000000000000) + (90251259 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12933

/-! A coarse bound on the actual paper statistics constant at dimension 12934. -/
namespace BstLean.Part266.Row12934
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12932 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12932 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12932 128 ≤ (13186 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13186 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12934) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12934 : ℕ))
    (by norm_num : (12934 : ℕ) ≤ 16384)
  have ht : paperTail256 12934 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12934 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12934 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12934 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12934 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12934 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12932 128 * √(2 / (12934 : ℝ)) *
      (√(12934 : ℝ) + paperT0 12934 + paperTail256 12934) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12934 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12934 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12934 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12932 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12932 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12934 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12934

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12934
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12934 (61 / 100) 164 (17 / (100 * 12934)) (26 / (10 * 12934)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12934 (61 / 100) 164 (17 / (100 * 12934)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (112786837 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1395229177 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (883568647 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12934 / 12934 * (61 / 100)) ^ 4 * inverseRadius8 (12934 - 1) /
            envelopeGap 12934 (61 / 100) 164 (17 / (100 * 12934)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12934

namespace BstLean.Part266.Row12934
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12934 164 ≤ (2189110053 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12934 164 ≤ (182581037 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (351067363 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12934 164 ≤ (1735485629 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12934 164 ≤ (617382431 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12934 164 ≤ (112787907 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (112786837 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (112786837 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1395229177 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (883568647 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3625417 / 1000000000) : ℝ) ≤ √(17 / (100 * 12934) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12934) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (531005737 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18676383329 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12934) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12934) ≤ (54670387 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12934) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12934 * (164 : ℝ) ^ 2 + 26 / (10 * 12934) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12934) : ℝ)) (tA 12934 * 164 ^ 2 + 26 / (10 * 12934)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3625417 / 1000000000))) * ((112786837 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3625417 / 1000000000)) ^ 3) * ((1395229177 / 1000000000000000000000000))) + ((883568647 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3625417 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12934) : ℝ)) d.D d.V d.P (√(tA 12934) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3625417 / 1000000000)) ^ 2 * (((531005737 / 250000000000000)) * ((18676383329 / 500000000000000000)))) + ((883568647 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12934) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3625417 / 1000000000)) * ((112786837 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12934) : ℝ)) (tA 12934 * 164 ^ 2 + 26 / (10 * 12934)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((112786837 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3625417 / 1000000000)) ^ 2) * ((1395229177 / 1000000000000000000000000)) + ((883568647 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12934) : ℝ)) (√(26 / (10 * 12934) : ℝ)) d.D d.V d.P (√(tA 12934) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3625417 / 1000000000)) * (((531005737 / 250000000000000)) * ((18676383329 / 500000000000000000))) + ((883568647 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12934) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((112786837 / 25000000000000000000) : ℝ) + ((883568647 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12934

namespace BstLean.Part266.Row12934
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12934 164 ∧
    0 ≤ (tableEnvelope C).f1 12934 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12934 164 ∧
    0 ≤ (tableEnvelope C).w1 12934 164 ∧ 0 ≤ (tableEnvelope C).w2 12934 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12934 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12934 164 ∧ 0 ≤ d.f1 12934 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12934 164 ∧ 0 ≤ d.w1 12934 164 ∧ 0 ≤ d.w2 12934 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12934 ≤ 2 * (228 / 100 : ℝ) / 12934 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12934 ≤ 2 * (370 / 100 : ℝ) / 12934 := by
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
    (completeRAData (tableEnvelope C) 12934 164).locationBound 12934 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12934 164).energyBound 12934 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12934 164) (d.f1 12934 164) d.f2 ≤
      32 * (((2189110053 / 500000000000000000) : ℝ) + (182581037 / 125000000000000000) + (351067363 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12934 164) (d.w1 12934 164)
      (d.w2 12934 164) ≤
      32 * (((1735485629 / 100000000000000000000) : ℝ) + (617382431 / 50000000000000000000) + (112787907 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12934 164) (d.f1 12934 164) d.f2 ≤
      ((2189110053 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2189110053 / 500000000000000000)) * ((182581037 / 125000000000000000)) * (126 / 100) +
      2 * (((182581037 / 125000000000000000)) ^ 2 + 2 * ((2189110053 / 500000000000000000)) * ((351067363 / 1000000000000000000))) +
      6 * ((182581037 / 125000000000000000)) * ((351067363 / 1000000000000000000)) * (126 / 100) + 8 * ((351067363 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12934 164) (d.f1 12934 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12934 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12934 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12934 164) (d.f1 12934 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12934 164) (d.w1 12934 164) (d.w2 12934 164)
  have hwexpr0 : 0 ≤ d.w0 12934 164 + d.w1 12934 164 * √(π / 2) +
      2 * d.w2 12934 164 + energyR16 12934 *
      radiusPolynomialRoot16 (d.w0 12934 164) (d.w1 12934 164) (d.w2 12934 164) := by
    positivity
  constructor
  · change (12934 : ℝ) ^ 8 * (mA 12934 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12934 164) (d.f1 12934 164) d.f2 + locationR16 12934 *
        radiusPolynomialRoot16 (d.f0 12934 164) (d.f1 12934 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12934 : ℝ) ^ 8 * (mA 12934 : ℝ) ^ 8 *
        ((((2189110053 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2189110053 / 500000000000000000)) * ((182581037 / 125000000000000000)) * (126 / 100) +
          2 * (((182581037 / 125000000000000000)) ^ 2 + 2 * ((2189110053 / 500000000000000000)) * ((351067363 / 1000000000000000000))) +
          6 * ((182581037 / 125000000000000000)) * ((351067363 / 1000000000000000000)) * (126 / 100) + 8 * ((351067363 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12934) *
          (32 * (((2189110053 / 500000000000000000) : ℝ) + (182581037 / 125000000000000000) + (351067363 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12934 : ℝ) ^ 16 *
      (d.w0 12934 164 + d.w1 12934 164 * √(π / 2) + 2 * d.w2 12934 164 +
        energyR16 12934 * radiusPolynomialRoot16 (d.w0 12934 164) (d.w1 12934 164)
          (d.w2 12934 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12934 : ℝ) ^ 16 *
        (((1735485629 / 100000000000000000000) : ℝ) + ((617382431 / 50000000000000000000)) * (126 / 100) + 2 * ((112787907 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12934) *
          (32 * (((1735485629 / 100000000000000000000) : ℝ) + (617382431 / 50000000000000000000) + (112787907 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12934

/-! A coarse bound on the actual paper statistics constant at dimension 12935. -/
namespace BstLean.Part266.Row12935
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12933 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12933 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12933 128 ≤ (13187 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13187 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12935) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12935 : ℕ))
    (by norm_num : (12935 : ℕ) ≤ 16384)
  have ht : paperTail256 12935 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12935 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12935 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12935 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12935 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12935 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12933 128 * √(2 / (12935 : ℝ)) *
      (√(12935 : ℝ) + paperT0 12935 + paperTail256 12935) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12935 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12935 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12935 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12933 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12933 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12935 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12935

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12935
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12935 (61 / 100) 164 (17 / (100 * 12935)) (26 / (10 * 12935)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12935 (61 / 100) 164 (17 / (100 * 12935)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (451042717 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (174349719 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (55188571 / 12500000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12935 / 12935 * (61 / 100)) ^ 4 * inverseRadius8 (12935 - 1) /
            envelopeGap 12935 (61 / 100) 164 (17 / (100 * 12935)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12935

namespace BstLean.Part266.Row12935
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12935 164 ≤ (437737341 / 100000000000000000)
  f1 : (tableEnvelope C).f1 12935 164 ≤ (11682927 / 8000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (350999497 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12935 164 ≤ (173508303 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12935 164 ≤ (308619611 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12935 164 ≤ (225523497 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (451042717 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (451042717 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (174349719 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (55188571 / 12500000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3625277 / 1000000000) : ℝ) ≤ √(17 / (100 * 12935) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12935) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (212377663 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7469398241 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12935) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12935) ≤ (109332321 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12935) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12935 * (164 : ℝ) ^ 2 + 26 / (10 * 12935) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12935) : ℝ)) (tA 12935 * 164 ^ 2 + 26 / (10 * 12935)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3625277 / 1000000000))) * ((451042717 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3625277 / 1000000000)) ^ 3) * ((174349719 / 125000000000000000000000))) + ((55188571 / 12500000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3625277 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12935) : ℝ)) d.D d.V d.P (√(tA 12935) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3625277 / 1000000000)) ^ 2 * (((212377663 / 100000000000000)) * ((7469398241 / 200000000000000000)))) + ((55188571 / 12500000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12935) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3625277 / 1000000000)) * ((451042717 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12935) : ℝ)) (tA 12935 * 164 ^ 2 + 26 / (10 * 12935)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((451042717 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3625277 / 1000000000)) ^ 2) * ((174349719 / 125000000000000000000000)) + ((55188571 / 12500000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12935) : ℝ)) (√(26 / (10 * 12935) : ℝ)) d.D d.V d.P (√(tA 12935) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3625277 / 1000000000)) * (((212377663 / 100000000000000)) * ((7469398241 / 200000000000000000))) + ((55188571 / 12500000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12935) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((451042717 / 100000000000000000000) : ℝ) + ((55188571 / 12500000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12935

namespace BstLean.Part266.Row12935
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12935 164 ∧
    0 ≤ (tableEnvelope C).f1 12935 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12935 164 ∧
    0 ≤ (tableEnvelope C).w1 12935 164 ∧ 0 ≤ (tableEnvelope C).w2 12935 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12935 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12935 164 ∧ 0 ≤ d.f1 12935 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12935 164 ∧ 0 ≤ d.w1 12935 164 ∧ 0 ≤ d.w2 12935 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12935 ≤ 2 * (228 / 100 : ℝ) / 12935 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12935 ≤ 2 * (370 / 100 : ℝ) / 12935 := by
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
    (completeRAData (tableEnvelope C) 12935 164).locationBound 12935 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12935 164).energyBound 12935 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12935 164) (d.f1 12935 164) d.f2 ≤
      32 * (((437737341 / 100000000000000000) : ℝ) + (11682927 / 8000000000000000) + (350999497 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12935 164) (d.w1 12935 164)
      (d.w2 12935 164) ≤
      32 * (((173508303 / 10000000000000000000) : ℝ) + (308619611 / 25000000000000000000) + (225523497 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12935 164) (d.f1 12935 164) d.f2 ≤
      ((437737341 / 100000000000000000) : ℝ) ^ 2 + 2 * ((437737341 / 100000000000000000)) * ((11682927 / 8000000000000000)) * (126 / 100) +
      2 * (((11682927 / 8000000000000000)) ^ 2 + 2 * ((437737341 / 100000000000000000)) * ((350999497 / 1000000000000000000))) +
      6 * ((11682927 / 8000000000000000)) * ((350999497 / 1000000000000000000)) * (126 / 100) + 8 * ((350999497 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12935 164) (d.f1 12935 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12935 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12935 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12935 164) (d.f1 12935 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12935 164) (d.w1 12935 164) (d.w2 12935 164)
  have hwexpr0 : 0 ≤ d.w0 12935 164 + d.w1 12935 164 * √(π / 2) +
      2 * d.w2 12935 164 + energyR16 12935 *
      radiusPolynomialRoot16 (d.w0 12935 164) (d.w1 12935 164) (d.w2 12935 164) := by
    positivity
  constructor
  · change (12935 : ℝ) ^ 8 * (mA 12935 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12935 164) (d.f1 12935 164) d.f2 + locationR16 12935 *
        radiusPolynomialRoot16 (d.f0 12935 164) (d.f1 12935 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12935 : ℝ) ^ 8 * (mA 12935 : ℝ) ^ 8 *
        ((((437737341 / 100000000000000000) : ℝ) ^ 2 + 2 * ((437737341 / 100000000000000000)) * ((11682927 / 8000000000000000)) * (126 / 100) +
          2 * (((11682927 / 8000000000000000)) ^ 2 + 2 * ((437737341 / 100000000000000000)) * ((350999497 / 1000000000000000000))) +
          6 * ((11682927 / 8000000000000000)) * ((350999497 / 1000000000000000000)) * (126 / 100) + 8 * ((350999497 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12935) *
          (32 * (((437737341 / 100000000000000000) : ℝ) + (11682927 / 8000000000000000) + (350999497 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12935 : ℝ) ^ 16 *
      (d.w0 12935 164 + d.w1 12935 164 * √(π / 2) + 2 * d.w2 12935 164 +
        energyR16 12935 * radiusPolynomialRoot16 (d.w0 12935 164) (d.w1 12935 164)
          (d.w2 12935 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12935 : ℝ) ^ 16 *
        (((173508303 / 10000000000000000000) : ℝ) + ((308619611 / 25000000000000000000)) * (126 / 100) + 2 * ((225523497 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12935) *
          (32 * (((173508303 / 10000000000000000000) : ℝ) + (308619611 / 25000000000000000000) + (225523497 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12935

/-! A coarse bound on the actual paper statistics constant at dimension 12936. -/
namespace BstLean.Part266.Row12936
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12934 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12934 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12934 128 ≤ (13188 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13188 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12936) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12936 : ℕ))
    (by norm_num : (12936 : ℕ) ≤ 16384)
  have ht : paperTail256 12936 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12936 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12936 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12936 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12936 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12936 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12934 128 * √(2 / (12936 : ℝ)) *
      (√(12936 : ℝ) + paperT0 12936 + paperTail256 12936) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12936 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12936 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12936 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12934 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12934 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12936 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12936

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12936
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12936 (61 / 100) 164 (17 / (100 * 12936)) (26 / (10 * 12936)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12936 (61 / 100) 164 (17 / (100 * 12936)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (225469059 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (697183247 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2206165031 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12936 / 12936 * (61 / 100)) ^ 4 * inverseRadius8 (12936 - 1) /
            envelopeGap 12936 (61 / 100) 164 (17 / (100 * 12936)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12936

namespace BstLean.Part266.Row12936
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12936 164 ≤ (4376527 / 1000000000000000)
  f1 : (tableEnvelope C).f1 12936 164 ≤ (1460083543 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (350931651 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12936 164 ≤ (867340283 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12936 164 ≤ (1234192119 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12936 164 ≤ (450942393 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (225469059 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (225469059 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (697183247 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2206165031 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3625137 / 1000000000) : ℝ) ≤ √(17 / (100 * 12936) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12936) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1061765179 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18670608547 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12936) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12936) ≤ (109323869 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12936) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12936 * (164 : ℝ) ^ 2 + 26 / (10 * 12936) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12936) : ℝ)) (tA 12936 * 164 ^ 2 + 26 / (10 * 12936)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3625137 / 1000000000))) * ((225469059 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3625137 / 1000000000)) ^ 3) * ((697183247 / 500000000000000000000000))) + ((2206165031 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3625137 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12936) : ℝ)) d.D d.V d.P (√(tA 12936) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3625137 / 1000000000)) ^ 2 * (((1061765179 / 500000000000000)) * ((18670608547 / 500000000000000000)))) + ((2206165031 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12936) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3625137 / 1000000000)) * ((225469059 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12936) : ℝ)) (tA 12936 * 164 ^ 2 + 26 / (10 * 12936)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((225469059 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3625137 / 1000000000)) ^ 2) * ((697183247 / 500000000000000000000000)) + ((2206165031 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12936) : ℝ)) (√(26 / (10 * 12936) : ℝ)) d.D d.V d.P (√(tA 12936) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3625137 / 1000000000)) * (((1061765179 / 500000000000000)) * ((18670608547 / 500000000000000000))) + ((2206165031 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12936) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((225469059 / 50000000000000000000) : ℝ) + ((2206165031 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12936

namespace BstLean.Part266.Row12936
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12936 164 ∧
    0 ≤ (tableEnvelope C).f1 12936 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12936 164 ∧
    0 ≤ (tableEnvelope C).w1 12936 164 ∧ 0 ≤ (tableEnvelope C).w2 12936 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12936 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12936 164 ∧ 0 ≤ d.f1 12936 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12936 164 ∧ 0 ≤ d.w1 12936 164 ∧ 0 ≤ d.w2 12936 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12936 ≤ 2 * (228 / 100 : ℝ) / 12936 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12936 ≤ 2 * (370 / 100 : ℝ) / 12936 := by
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
    (completeRAData (tableEnvelope C) 12936 164).locationBound 12936 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12936 164).energyBound 12936 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12936 164) (d.f1 12936 164) d.f2 ≤
      32 * (((4376527 / 1000000000000000) : ℝ) + (1460083543 / 1000000000000000000) + (350931651 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12936 164) (d.w1 12936 164)
      (d.w2 12936 164) ≤
      32 * (((867340283 / 50000000000000000000) : ℝ) + (1234192119 / 100000000000000000000) + (450942393 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12936 164) (d.f1 12936 164) d.f2 ≤
      ((4376527 / 1000000000000000) : ℝ) ^ 2 + 2 * ((4376527 / 1000000000000000)) * ((1460083543 / 1000000000000000000)) * (126 / 100) +
      2 * (((1460083543 / 1000000000000000000)) ^ 2 + 2 * ((4376527 / 1000000000000000)) * ((350931651 / 1000000000000000000))) +
      6 * ((1460083543 / 1000000000000000000)) * ((350931651 / 1000000000000000000)) * (126 / 100) + 8 * ((350931651 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12936 164) (d.f1 12936 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12936 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12936 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12936 164) (d.f1 12936 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12936 164) (d.w1 12936 164) (d.w2 12936 164)
  have hwexpr0 : 0 ≤ d.w0 12936 164 + d.w1 12936 164 * √(π / 2) +
      2 * d.w2 12936 164 + energyR16 12936 *
      radiusPolynomialRoot16 (d.w0 12936 164) (d.w1 12936 164) (d.w2 12936 164) := by
    positivity
  constructor
  · change (12936 : ℝ) ^ 8 * (mA 12936 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12936 164) (d.f1 12936 164) d.f2 + locationR16 12936 *
        radiusPolynomialRoot16 (d.f0 12936 164) (d.f1 12936 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12936 : ℝ) ^ 8 * (mA 12936 : ℝ) ^ 8 *
        ((((4376527 / 1000000000000000) : ℝ) ^ 2 + 2 * ((4376527 / 1000000000000000)) * ((1460083543 / 1000000000000000000)) * (126 / 100) +
          2 * (((1460083543 / 1000000000000000000)) ^ 2 + 2 * ((4376527 / 1000000000000000)) * ((350931651 / 1000000000000000000))) +
          6 * ((1460083543 / 1000000000000000000)) * ((350931651 / 1000000000000000000)) * (126 / 100) + 8 * ((350931651 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12936) *
          (32 * (((4376527 / 1000000000000000) : ℝ) + (1460083543 / 1000000000000000000) + (350931651 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12936 : ℝ) ^ 16 *
      (d.w0 12936 164 + d.w1 12936 164 * √(π / 2) + 2 * d.w2 12936 164 +
        energyR16 12936 * radiusPolynomialRoot16 (d.w0 12936 164) (d.w1 12936 164)
          (d.w2 12936 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12936 : ℝ) ^ 16 *
        (((867340283 / 50000000000000000000) : ℝ) + ((1234192119 / 100000000000000000000)) * (126 / 100) + 2 * ((450942393 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12936) *
          (32 * (((867340283 / 50000000000000000000) : ℝ) + (1234192119 / 100000000000000000000) + (450942393 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12936

/-! A coarse bound on the actual paper statistics constant at dimension 12937. -/
namespace BstLean.Part266.Row12937
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12935 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12935 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12935 128 ≤ (13189 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13189 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12937) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12937 : ℕ))
    (by norm_num : (12937 : ℕ) ≤ 16384)
  have ht : paperTail256 12937 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12937 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12937 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12937 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12937 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12937 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12935 128 * √(2 / (12937 : ℝ)) *
      (√(12937 : ℝ) + paperT0 12937 + paperTail256 12937) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12937 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12937 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12937 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12935 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12935 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12937 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12937

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12937
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12937 (61 / 100) 164 (17 / (100 * 12937)) (26 / (10 * 12937)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12937 (61 / 100) 164 (17 / (100 * 12937)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (450833551 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (696967701 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4409576381 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12937 / 12937 * (61 / 100)) ^ 4 * inverseRadius8 (12937 - 1) /
            envelopeGap 12937 (61 / 100) 164 (17 / (100 * 12937)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12937

namespace BstLean.Part266.Row12937
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12937 164 ≤ (35005447 / 8000000000000000)
  f1 : (tableEnvelope C).f1 12937 164 ≤ (14598013 / 10000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (14034553 / 40000000000000000)
  w0 : (tableEnvelope C).w0 12937 164 ≤ (1734278237 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12937 164 ≤ (38559559 / 3125000000000000000)
  w2 : (tableEnvelope C).w2 12937 164 ≤ (450837823 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (450833551 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (450833551 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (696967701 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4409576381 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3624997 / 1000000000) : ℝ) ≤ √(17 / (100 * 12937) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12937) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1061642067 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37335444313 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12937) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12937) ≤ (54657709 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12937) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12937 * (164 : ℝ) ^ 2 + 26 / (10 * 12937) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12937) : ℝ)) (tA 12937 * 164 ^ 2 + 26 / (10 * 12937)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3624997 / 1000000000))) * ((450833551 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3624997 / 1000000000)) ^ 3) * ((696967701 / 500000000000000000000000))) + ((4409576381 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3624997 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12937) : ℝ)) d.D d.V d.P (√(tA 12937) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3624997 / 1000000000)) ^ 2 * (((1061642067 / 500000000000000)) * ((37335444313 / 1000000000000000000)))) + ((4409576381 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12937) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3624997 / 1000000000)) * ((450833551 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12937) : ℝ)) (tA 12937 * 164 ^ 2 + 26 / (10 * 12937)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((450833551 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3624997 / 1000000000)) ^ 2) * ((696967701 / 500000000000000000000000)) + ((4409576381 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12937) : ℝ)) (√(26 / (10 * 12937) : ℝ)) d.D d.V d.P (√(tA 12937) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3624997 / 1000000000)) * (((1061642067 / 500000000000000)) * ((37335444313 / 1000000000000000000))) + ((4409576381 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12937) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((450833551 / 100000000000000000000) : ℝ) + ((4409576381 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12937

namespace BstLean.Part266.Row12937
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12937 164 ∧
    0 ≤ (tableEnvelope C).f1 12937 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12937 164 ∧
    0 ≤ (tableEnvelope C).w1 12937 164 ∧ 0 ≤ (tableEnvelope C).w2 12937 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12937 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12937 164 ∧ 0 ≤ d.f1 12937 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12937 164 ∧ 0 ≤ d.w1 12937 164 ∧ 0 ≤ d.w2 12937 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12937 ≤ 2 * (228 / 100 : ℝ) / 12937 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12937 ≤ 2 * (370 / 100 : ℝ) / 12937 := by
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
    (completeRAData (tableEnvelope C) 12937 164).locationBound 12937 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12937 164).energyBound 12937 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12937 164) (d.f1 12937 164) d.f2 ≤
      32 * (((35005447 / 8000000000000000) : ℝ) + (14598013 / 10000000000000000) + (14034553 / 40000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12937 164) (d.w1 12937 164)
      (d.w2 12937 164) ≤
      32 * (((1734278237 / 100000000000000000000) : ℝ) + (38559559 / 3125000000000000000) + (450837823 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12937 164) (d.f1 12937 164) d.f2 ≤
      ((35005447 / 8000000000000000) : ℝ) ^ 2 + 2 * ((35005447 / 8000000000000000)) * ((14598013 / 10000000000000000)) * (126 / 100) +
      2 * (((14598013 / 10000000000000000)) ^ 2 + 2 * ((35005447 / 8000000000000000)) * ((14034553 / 40000000000000000))) +
      6 * ((14598013 / 10000000000000000)) * ((14034553 / 40000000000000000)) * (126 / 100) + 8 * ((14034553 / 40000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12937 164) (d.f1 12937 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12937 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12937 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12937 164) (d.f1 12937 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12937 164) (d.w1 12937 164) (d.w2 12937 164)
  have hwexpr0 : 0 ≤ d.w0 12937 164 + d.w1 12937 164 * √(π / 2) +
      2 * d.w2 12937 164 + energyR16 12937 *
      radiusPolynomialRoot16 (d.w0 12937 164) (d.w1 12937 164) (d.w2 12937 164) := by
    positivity
  constructor
  · change (12937 : ℝ) ^ 8 * (mA 12937 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12937 164) (d.f1 12937 164) d.f2 + locationR16 12937 *
        radiusPolynomialRoot16 (d.f0 12937 164) (d.f1 12937 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12937 : ℝ) ^ 8 * (mA 12937 : ℝ) ^ 8 *
        ((((35005447 / 8000000000000000) : ℝ) ^ 2 + 2 * ((35005447 / 8000000000000000)) * ((14598013 / 10000000000000000)) * (126 / 100) +
          2 * (((14598013 / 10000000000000000)) ^ 2 + 2 * ((35005447 / 8000000000000000)) * ((14034553 / 40000000000000000))) +
          6 * ((14598013 / 10000000000000000)) * ((14034553 / 40000000000000000)) * (126 / 100) + 8 * ((14034553 / 40000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12937) *
          (32 * (((35005447 / 8000000000000000) : ℝ) + (14598013 / 10000000000000000) + (14034553 / 40000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12937 : ℝ) ^ 16 *
      (d.w0 12937 164 + d.w1 12937 164 * √(π / 2) + 2 * d.w2 12937 164 +
        energyR16 12937 * radiusPolynomialRoot16 (d.w0 12937 164) (d.w1 12937 164)
          (d.w2 12937 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12937 : ℝ) ^ 16 *
        (((1734278237 / 100000000000000000000) : ℝ) + ((38559559 / 3125000000000000000)) * (126 / 100) + 2 * ((450837823 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12937) *
          (32 * (((1734278237 / 100000000000000000000) : ℝ) + (38559559 / 3125000000000000000) + (450837823 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12937

/-! A coarse bound on the actual paper statistics constant at dimension 12938. -/
namespace BstLean.Part266.Row12938
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12936 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12936 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12936 128 ≤ (13190 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13190 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12938) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12938 : ℕ))
    (by norm_num : (12938 : ℕ) ≤ 16384)
  have ht : paperTail256 12938 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12938 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12938 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12938 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12938 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12938 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12936 128 * √(2 / (12938 : ℝ)) *
      (√(12938 : ℝ) + paperT0 12938 + paperTail256 12938) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12938 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12938 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12938 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12936 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12936 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12938 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12938

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12938
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12938 (61 / 100) 164 (17 / (100 * 12938)) (26 / (10 * 12938)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12938 (61 / 100) 164 (17 / (100 * 12938)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (450729017 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (348376119 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1101706159 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12938 / 12938 * (61 / 100)) ^ 4 * inverseRadius8 (12938 - 1) /
            envelopeGap 12938 (61 / 100) 164 (17 / (100 * 12938)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12938

namespace BstLean.Part266.Row12938
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12938 164 ≤ (4374835033 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12938 164 ≤ (1459519147 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (175398009 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12938 164 ≤ (346775209 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12938 164 ≤ (1233619751 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12938 164 ≤ (225366643 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (450729017 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (450729017 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (348376119 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1101706159 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3624857 / 1000000000) : ℝ) ≤ √(17 / (100 * 12938) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12938) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1061518979 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37329672863 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12938) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12938) ≤ (109306969 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12938) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12938 * (164 : ℝ) ^ 2 + 26 / (10 * 12938) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12938) : ℝ)) (tA 12938 * 164 ^ 2 + 26 / (10 * 12938)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3624857 / 1000000000))) * ((450729017 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3624857 / 1000000000)) ^ 3) * ((348376119 / 250000000000000000000000))) + ((1101706159 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3624857 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12938) : ℝ)) d.D d.V d.P (√(tA 12938) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3624857 / 1000000000)) ^ 2 * (((1061518979 / 500000000000000)) * ((37329672863 / 1000000000000000000)))) + ((1101706159 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12938) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3624857 / 1000000000)) * ((450729017 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12938) : ℝ)) (tA 12938 * 164 ^ 2 + 26 / (10 * 12938)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((450729017 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3624857 / 1000000000)) ^ 2) * ((348376119 / 250000000000000000000000)) + ((1101706159 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12938) : ℝ)) (√(26 / (10 * 12938) : ℝ)) d.D d.V d.P (√(tA 12938) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3624857 / 1000000000)) * (((1061518979 / 500000000000000)) * ((37329672863 / 1000000000000000000))) + ((1101706159 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12938) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((450729017 / 100000000000000000000) : ℝ) + ((1101706159 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12938

namespace BstLean.Part266.Row12938
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12938 164 ∧
    0 ≤ (tableEnvelope C).f1 12938 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12938 164 ∧
    0 ≤ (tableEnvelope C).w1 12938 164 ∧ 0 ≤ (tableEnvelope C).w2 12938 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12938 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12938 164 ∧ 0 ≤ d.f1 12938 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12938 164 ∧ 0 ≤ d.w1 12938 164 ∧ 0 ≤ d.w2 12938 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12938 ≤ 2 * (228 / 100 : ℝ) / 12938 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12938 ≤ 2 * (370 / 100 : ℝ) / 12938 := by
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
    (completeRAData (tableEnvelope C) 12938 164).locationBound 12938 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12938 164).energyBound 12938 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12938 164) (d.f1 12938 164) d.f2 ≤
      32 * (((4374835033 / 1000000000000000000) : ℝ) + (1459519147 / 1000000000000000000) + (175398009 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12938 164) (d.w1 12938 164)
      (d.w2 12938 164) ≤
      32 * (((346775209 / 20000000000000000000) : ℝ) + (1233619751 / 100000000000000000000) + (225366643 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12938 164) (d.f1 12938 164) d.f2 ≤
      ((4374835033 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4374835033 / 1000000000000000000)) * ((1459519147 / 1000000000000000000)) * (126 / 100) +
      2 * (((1459519147 / 1000000000000000000)) ^ 2 + 2 * ((4374835033 / 1000000000000000000)) * ((175398009 / 500000000000000000))) +
      6 * ((1459519147 / 1000000000000000000)) * ((175398009 / 500000000000000000)) * (126 / 100) + 8 * ((175398009 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12938 164) (d.f1 12938 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12938 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12938 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12938 164) (d.f1 12938 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12938 164) (d.w1 12938 164) (d.w2 12938 164)
  have hwexpr0 : 0 ≤ d.w0 12938 164 + d.w1 12938 164 * √(π / 2) +
      2 * d.w2 12938 164 + energyR16 12938 *
      radiusPolynomialRoot16 (d.w0 12938 164) (d.w1 12938 164) (d.w2 12938 164) := by
    positivity
  constructor
  · change (12938 : ℝ) ^ 8 * (mA 12938 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12938 164) (d.f1 12938 164) d.f2 + locationR16 12938 *
        radiusPolynomialRoot16 (d.f0 12938 164) (d.f1 12938 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12938 : ℝ) ^ 8 * (mA 12938 : ℝ) ^ 8 *
        ((((4374835033 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4374835033 / 1000000000000000000)) * ((1459519147 / 1000000000000000000)) * (126 / 100) +
          2 * (((1459519147 / 1000000000000000000)) ^ 2 + 2 * ((4374835033 / 1000000000000000000)) * ((175398009 / 500000000000000000))) +
          6 * ((1459519147 / 1000000000000000000)) * ((175398009 / 500000000000000000)) * (126 / 100) + 8 * ((175398009 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12938) *
          (32 * (((4374835033 / 1000000000000000000) : ℝ) + (1459519147 / 1000000000000000000) + (175398009 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12938 : ℝ) ^ 16 *
      (d.w0 12938 164 + d.w1 12938 164 * √(π / 2) + 2 * d.w2 12938 164 +
        energyR16 12938 * radiusPolynomialRoot16 (d.w0 12938 164) (d.w1 12938 164)
          (d.w2 12938 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12938 : ℝ) ^ 16 *
        (((346775209 / 20000000000000000000) : ℝ) + ((1233619751 / 100000000000000000000)) * (126 / 100) + 2 * ((225366643 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12938) *
          (32 * (((346775209 / 20000000000000000000) : ℝ) + (1233619751 / 100000000000000000000) + (225366643 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12938

/-! A coarse bound on the actual paper statistics constant at dimension 12939. -/
namespace BstLean.Part266.Row12939
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12937 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12937 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12937 128 ≤ (13191 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13191 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12939) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12939 : ℕ))
    (by norm_num : (12939 : ℕ) ≤ 16384)
  have ht : paperTail256 12939 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12939 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12939 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12939 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12939 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12939 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12937 128 * √(2 / (12939 : ℝ)) *
      (√(12939 : ℝ) + paperT0 12939 + paperTail256 12939) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12939 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12939 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12939 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12937 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12937 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12939 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12939

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12939
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12939 (61 / 100) 164 (17 / (100 * 12939)) (26 / (10 * 12939)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12939 (61 / 100) 164 (17 / (100 * 12939)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (90124903 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (696536859 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (550509353 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12939 / 12939 * (61 / 100)) ^ 4 * inverseRadius8 (12939 - 1) /
            envelopeGap 12939 (61 / 100) 164 (17 / (100 * 12939)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12939

namespace BstLean.Part266.Row12939
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12939 164 ≤ (1093498241 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12939 164 ≤ (1459237889 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (350728329 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12939 164 ≤ (1733474697 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12939 164 ≤ (1233334049 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12939 164 ≤ (225314391 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (90124903 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (90124903 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (696536859 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (550509353 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((906179 / 250000000) : ℝ) ≤ √(17 / (100 * 12939) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12939) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (212279183 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37323902771 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12939) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12939) ≤ (109298521 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12939) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12939 * (164 : ℝ) ^ 2 + 26 / (10 * 12939) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12939) : ℝ)) (tA 12939 * 164 ^ 2 + 26 / (10 * 12939)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((906179 / 250000000))) * ((90124903 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((906179 / 250000000)) ^ 3) * ((696536859 / 500000000000000000000000))) + ((550509353 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((906179 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12939) : ℝ)) d.D d.V d.P (√(tA 12939) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((906179 / 250000000)) ^ 2 * (((212279183 / 100000000000000)) * ((37323902771 / 1000000000000000000)))) + ((550509353 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12939) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((906179 / 250000000)) * ((90124903 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12939) : ℝ)) (tA 12939 * 164 ^ 2 + 26 / (10 * 12939)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((90124903 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((906179 / 250000000)) ^ 2) * ((696536859 / 500000000000000000000000)) + ((550509353 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12939) : ℝ)) (√(26 / (10 * 12939) : ℝ)) d.D d.V d.P (√(tA 12939) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((906179 / 250000000)) * (((212279183 / 100000000000000)) * ((37323902771 / 1000000000000000000))) + ((550509353 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12939) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((90124903 / 20000000000000000000) : ℝ) + ((550509353 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12939

namespace BstLean.Part266.Row12939
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12939 164 ∧
    0 ≤ (tableEnvelope C).f1 12939 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12939 164 ∧
    0 ≤ (tableEnvelope C).w1 12939 164 ∧ 0 ≤ (tableEnvelope C).w2 12939 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12939 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12939 164 ∧ 0 ≤ d.f1 12939 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12939 164 ∧ 0 ≤ d.w1 12939 164 ∧ 0 ≤ d.w2 12939 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12939 ≤ 2 * (228 / 100 : ℝ) / 12939 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12939 ≤ 2 * (370 / 100 : ℝ) / 12939 := by
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
    (completeRAData (tableEnvelope C) 12939 164).locationBound 12939 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12939 164).energyBound 12939 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12939 164) (d.f1 12939 164) d.f2 ≤
      32 * (((1093498241 / 250000000000000000) : ℝ) + (1459237889 / 1000000000000000000) + (350728329 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12939 164) (d.w1 12939 164)
      (d.w2 12939 164) ≤
      32 * (((1733474697 / 100000000000000000000) : ℝ) + (1233334049 / 100000000000000000000) + (225314391 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12939 164) (d.f1 12939 164) d.f2 ≤
      ((1093498241 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1093498241 / 250000000000000000)) * ((1459237889 / 1000000000000000000)) * (126 / 100) +
      2 * (((1459237889 / 1000000000000000000)) ^ 2 + 2 * ((1093498241 / 250000000000000000)) * ((350728329 / 1000000000000000000))) +
      6 * ((1459237889 / 1000000000000000000)) * ((350728329 / 1000000000000000000)) * (126 / 100) + 8 * ((350728329 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12939 164) (d.f1 12939 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12939 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12939 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12939 164) (d.f1 12939 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12939 164) (d.w1 12939 164) (d.w2 12939 164)
  have hwexpr0 : 0 ≤ d.w0 12939 164 + d.w1 12939 164 * √(π / 2) +
      2 * d.w2 12939 164 + energyR16 12939 *
      radiusPolynomialRoot16 (d.w0 12939 164) (d.w1 12939 164) (d.w2 12939 164) := by
    positivity
  constructor
  · change (12939 : ℝ) ^ 8 * (mA 12939 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12939 164) (d.f1 12939 164) d.f2 + locationR16 12939 *
        radiusPolynomialRoot16 (d.f0 12939 164) (d.f1 12939 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12939 : ℝ) ^ 8 * (mA 12939 : ℝ) ^ 8 *
        ((((1093498241 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1093498241 / 250000000000000000)) * ((1459237889 / 1000000000000000000)) * (126 / 100) +
          2 * (((1459237889 / 1000000000000000000)) ^ 2 + 2 * ((1093498241 / 250000000000000000)) * ((350728329 / 1000000000000000000))) +
          6 * ((1459237889 / 1000000000000000000)) * ((350728329 / 1000000000000000000)) * (126 / 100) + 8 * ((350728329 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12939) *
          (32 * (((1093498241 / 250000000000000000) : ℝ) + (1459237889 / 1000000000000000000) + (350728329 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12939 : ℝ) ^ 16 *
      (d.w0 12939 164 + d.w1 12939 164 * √(π / 2) + 2 * d.w2 12939 164 +
        energyR16 12939 * radiusPolynomialRoot16 (d.w0 12939 164) (d.w1 12939 164)
          (d.w2 12939 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12939 : ℝ) ^ 16 *
        (((1733474697 / 100000000000000000000) : ℝ) + ((1233334049 / 100000000000000000000)) * (126 / 100) + 2 * ((225314391 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12939) *
          (32 * (((1733474697 / 100000000000000000000) : ℝ) + (1233334049 / 100000000000000000000) + (225314391 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12939

/-! A coarse bound on the actual paper statistics constant at dimension 12940. -/
namespace BstLean.Part266.Row12940
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12938 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12938 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12938 128 ≤ (13192 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13192 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12940) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12940 : ℕ))
    (by norm_num : (12940 : ℕ) ≤ 16384)
  have ht : paperTail256 12940 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12940 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12940 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12940 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12940 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12940 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12938 128 * √(2 / (12940 : ℝ)) *
      (√(12940 : ℝ) + paperT0 12940 + paperTail256 12940) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12940 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12940 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12940 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12938 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12938 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12940 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12940

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12940
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12940 (61 / 100) 164 (17 / (100 * 12940)) (26 / (10 * 12940)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12940 (61 / 100) 164 (17 / (100 * 12940)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (90104009 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (2228229 / 1600000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (137541467 / 31250000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12940 / 12940 * (61 / 100)) ^ 4 * inverseRadius8 (12940 - 1) /
            envelopeGap 12940 (61 / 100) 164 (17 / (100 * 12940)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12940

namespace BstLean.Part266.Row12940
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12940 164 ≤ (1093286923 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12940 164 ≤ (729477957 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (175330281 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12940 164 ≤ (69322911 / 4000000000000000000)
  w1 : (tableEnvelope C).w1 12940 164 ≤ (1233048099 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12940 164 ≤ (450524309 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (90104009 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (90104009 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (2228229 / 1600000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (137541467 / 31250000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((28317 / 7812500) : ℝ) ≤ √(17 / (100 * 12940) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12940) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (530636437 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37318133997 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12940) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12940) ≤ (4371603 / 40000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12940) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12940 * (164 : ℝ) ^ 2 + 26 / (10 * 12940) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12940) : ℝ)) (tA 12940 * 164 ^ 2 + 26 / (10 * 12940)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((28317 / 7812500))) * ((90104009 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((28317 / 7812500)) ^ 3) * ((2228229 / 1600000000000000000000))) + ((137541467 / 31250000000000000000000)) * (3 / 2 * (39895 / 100000) / ((28317 / 7812500)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12940) : ℝ)) d.D d.V d.P (√(tA 12940) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((28317 / 7812500)) ^ 2 * (((530636437 / 250000000000000)) * ((37318133997 / 1000000000000000000)))) + ((137541467 / 31250000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12940) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((28317 / 7812500)) * ((90104009 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12940) : ℝ)) (tA 12940 * 164 ^ 2 + 26 / (10 * 12940)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((90104009 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((28317 / 7812500)) ^ 2) * ((2228229 / 1600000000000000000000)) + ((137541467 / 31250000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12940) : ℝ)) (√(26 / (10 * 12940) : ℝ)) d.D d.V d.P (√(tA 12940) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((28317 / 7812500)) * (((530636437 / 250000000000000)) * ((37318133997 / 1000000000000000000))) + ((137541467 / 31250000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12940) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((90104009 / 20000000000000000000) : ℝ) + ((137541467 / 31250000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12940

namespace BstLean.Part266.Row12940
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12940 164 ∧
    0 ≤ (tableEnvelope C).f1 12940 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12940 164 ∧
    0 ≤ (tableEnvelope C).w1 12940 164 ∧ 0 ≤ (tableEnvelope C).w2 12940 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12940 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12940 164 ∧ 0 ≤ d.f1 12940 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12940 164 ∧ 0 ≤ d.w1 12940 164 ∧ 0 ≤ d.w2 12940 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12940 ≤ 2 * (228 / 100 : ℝ) / 12940 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12940 ≤ 2 * (370 / 100 : ℝ) / 12940 := by
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
    (completeRAData (tableEnvelope C) 12940 164).locationBound 12940 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12940 164).energyBound 12940 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12940 164) (d.f1 12940 164) d.f2 ≤
      32 * (((1093286923 / 250000000000000000) : ℝ) + (729477957 / 500000000000000000) + (175330281 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12940 164) (d.w1 12940 164)
      (d.w2 12940 164) ≤
      32 * (((69322911 / 4000000000000000000) : ℝ) + (1233048099 / 100000000000000000000) + (450524309 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12940 164) (d.f1 12940 164) d.f2 ≤
      ((1093286923 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1093286923 / 250000000000000000)) * ((729477957 / 500000000000000000)) * (126 / 100) +
      2 * (((729477957 / 500000000000000000)) ^ 2 + 2 * ((1093286923 / 250000000000000000)) * ((175330281 / 500000000000000000))) +
      6 * ((729477957 / 500000000000000000)) * ((175330281 / 500000000000000000)) * (126 / 100) + 8 * ((175330281 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12940 164) (d.f1 12940 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12940 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12940 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12940 164) (d.f1 12940 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12940 164) (d.w1 12940 164) (d.w2 12940 164)
  have hwexpr0 : 0 ≤ d.w0 12940 164 + d.w1 12940 164 * √(π / 2) +
      2 * d.w2 12940 164 + energyR16 12940 *
      radiusPolynomialRoot16 (d.w0 12940 164) (d.w1 12940 164) (d.w2 12940 164) := by
    positivity
  constructor
  · change (12940 : ℝ) ^ 8 * (mA 12940 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12940 164) (d.f1 12940 164) d.f2 + locationR16 12940 *
        radiusPolynomialRoot16 (d.f0 12940 164) (d.f1 12940 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12940 : ℝ) ^ 8 * (mA 12940 : ℝ) ^ 8 *
        ((((1093286923 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1093286923 / 250000000000000000)) * ((729477957 / 500000000000000000)) * (126 / 100) +
          2 * (((729477957 / 500000000000000000)) ^ 2 + 2 * ((1093286923 / 250000000000000000)) * ((175330281 / 500000000000000000))) +
          6 * ((729477957 / 500000000000000000)) * ((175330281 / 500000000000000000)) * (126 / 100) + 8 * ((175330281 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12940) *
          (32 * (((1093286923 / 250000000000000000) : ℝ) + (729477957 / 500000000000000000) + (175330281 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12940 : ℝ) ^ 16 *
      (d.w0 12940 164 + d.w1 12940 164 * √(π / 2) + 2 * d.w2 12940 164 +
        energyR16 12940 * radiusPolynomialRoot16 (d.w0 12940 164) (d.w1 12940 164)
          (d.w2 12940 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12940 : ℝ) ^ 16 *
        (((69322911 / 4000000000000000000) : ℝ) + ((1233048099 / 100000000000000000000)) * (126 / 100) + 2 * ((450524309 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12940) *
          (32 * (((69322911 / 4000000000000000000) : ℝ) + (1233048099 / 100000000000000000000) + (450524309 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12940

/-! A coarse bound on the actual paper statistics constant at dimension 12941. -/
namespace BstLean.Part266.Row12941
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12939 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12939 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12939 128 ≤ (13193 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13193 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12941) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12941 : ℕ))
    (by norm_num : (12941 : ℕ) ≤ 16384)
  have ht : paperTail256 12941 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12941 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12941 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12941 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12941 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12941 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12939 128 * √(2 / (12941 : ℝ)) *
      (√(12941 : ℝ) + paperT0 12941 + paperTail256 12941) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12941 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12941 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12941 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12939 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12939 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12941 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12941

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12941
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12941 (61 / 100) 164 (17 / (100 * 12941)) (26 / (10 * 12941)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12941 (61 / 100) 164 (17 / (100 * 12941)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (450415607 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (13922127 / 10000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2199290497 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12941 / 12941 * (61 / 100)) ^ 4 * inverseRadius8 (12941 - 1) /
            envelopeGap 12941 (61 / 100) 164 (17 / (100 * 12941)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12941

namespace BstLean.Part266.Row12941
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12941 164 ≤ (437230271 / 100000000000000000)
  f1 : (tableEnvelope C).f1 12941 164 ≤ (364668507 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (175296407 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12941 164 ≤ (173267099 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12941 164 ≤ (1232762243 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12941 164 ≤ (112604967 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (450415607 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (450415607 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (13922127 / 10000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2199290497 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((906109 / 250000000) : ℝ) ≤ √(17 / (100 * 12941) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12941) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2122299713 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37312366583 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12941) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12941) ≤ (10928163 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12941) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12941 * (164 : ℝ) ^ 2 + 26 / (10 * 12941) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12941) : ℝ)) (tA 12941 * 164 ^ 2 + 26 / (10 * 12941)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((906109 / 250000000))) * ((450415607 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((906109 / 250000000)) ^ 3) * ((13922127 / 10000000000000000000000))) + ((2199290497 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((906109 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12941) : ℝ)) d.D d.V d.P (√(tA 12941) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((906109 / 250000000)) ^ 2 * (((2122299713 / 1000000000000000)) * ((37312366583 / 1000000000000000000)))) + ((2199290497 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12941) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((906109 / 250000000)) * ((450415607 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12941) : ℝ)) (tA 12941 * 164 ^ 2 + 26 / (10 * 12941)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((450415607 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((906109 / 250000000)) ^ 2) * ((13922127 / 10000000000000000000000)) + ((2199290497 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12941) : ℝ)) (√(26 / (10 * 12941) : ℝ)) d.D d.V d.P (√(tA 12941) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((906109 / 250000000)) * (((2122299713 / 1000000000000000)) * ((37312366583 / 1000000000000000000))) + ((2199290497 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12941) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((450415607 / 100000000000000000000) : ℝ) + ((2199290497 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12941

namespace BstLean.Part266.Row12941
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12941 164 ∧
    0 ≤ (tableEnvelope C).f1 12941 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12941 164 ∧
    0 ≤ (tableEnvelope C).w1 12941 164 ∧ 0 ≤ (tableEnvelope C).w2 12941 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12941 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12941 164 ∧ 0 ≤ d.f1 12941 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12941 164 ∧ 0 ≤ d.w1 12941 164 ∧ 0 ≤ d.w2 12941 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12941 ≤ 2 * (228 / 100 : ℝ) / 12941 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12941 ≤ 2 * (370 / 100 : ℝ) / 12941 := by
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
    (completeRAData (tableEnvelope C) 12941 164).locationBound 12941 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12941 164).energyBound 12941 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12941 164) (d.f1 12941 164) d.f2 ≤
      32 * (((437230271 / 100000000000000000) : ℝ) + (364668507 / 250000000000000000) + (175296407 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12941 164) (d.w1 12941 164)
      (d.w2 12941 164) ≤
      32 * (((173267099 / 10000000000000000000) : ℝ) + (1232762243 / 100000000000000000000) + (112604967 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12941 164) (d.f1 12941 164) d.f2 ≤
      ((437230271 / 100000000000000000) : ℝ) ^ 2 + 2 * ((437230271 / 100000000000000000)) * ((364668507 / 250000000000000000)) * (126 / 100) +
      2 * (((364668507 / 250000000000000000)) ^ 2 + 2 * ((437230271 / 100000000000000000)) * ((175296407 / 500000000000000000))) +
      6 * ((364668507 / 250000000000000000)) * ((175296407 / 500000000000000000)) * (126 / 100) + 8 * ((175296407 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12941 164) (d.f1 12941 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12941 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12941 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12941 164) (d.f1 12941 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12941 164) (d.w1 12941 164) (d.w2 12941 164)
  have hwexpr0 : 0 ≤ d.w0 12941 164 + d.w1 12941 164 * √(π / 2) +
      2 * d.w2 12941 164 + energyR16 12941 *
      radiusPolynomialRoot16 (d.w0 12941 164) (d.w1 12941 164) (d.w2 12941 164) := by
    positivity
  constructor
  · change (12941 : ℝ) ^ 8 * (mA 12941 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12941 164) (d.f1 12941 164) d.f2 + locationR16 12941 *
        radiusPolynomialRoot16 (d.f0 12941 164) (d.f1 12941 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12941 : ℝ) ^ 8 * (mA 12941 : ℝ) ^ 8 *
        ((((437230271 / 100000000000000000) : ℝ) ^ 2 + 2 * ((437230271 / 100000000000000000)) * ((364668507 / 250000000000000000)) * (126 / 100) +
          2 * (((364668507 / 250000000000000000)) ^ 2 + 2 * ((437230271 / 100000000000000000)) * ((175296407 / 500000000000000000))) +
          6 * ((364668507 / 250000000000000000)) * ((175296407 / 500000000000000000)) * (126 / 100) + 8 * ((175296407 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12941) *
          (32 * (((437230271 / 100000000000000000) : ℝ) + (364668507 / 250000000000000000) + (175296407 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12941 : ℝ) ^ 16 *
      (d.w0 12941 164 + d.w1 12941 164 * √(π / 2) + 2 * d.w2 12941 164 +
        energyR16 12941 * radiusPolynomialRoot16 (d.w0 12941 164) (d.w1 12941 164)
          (d.w2 12941 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12941 : ℝ) ^ 16 *
        (((173267099 / 10000000000000000000) : ℝ) + ((1232762243 / 100000000000000000000)) * (126 / 100) + 2 * ((112604967 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12941) *
          (32 * (((173267099 / 10000000000000000000) : ℝ) + (1232762243 / 100000000000000000000) + (112604967 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12941

/-! A coarse bound on the actual paper statistics constant at dimension 12942. -/
namespace BstLean.Part266.Row12942
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12940 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12940 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12940 128 ≤ (13194 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13194 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12942) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12942 : ℕ))
    (by norm_num : (12942 : ℕ) ≤ 16384)
  have ht : paperTail256 12942 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12942 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12942 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12942 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12942 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12942 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12940 128 * √(2 / (12942 : ℝ)) *
      (√(12942 : ℝ) + paperT0 12942 + paperTail256 12942) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12942 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12942 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12942 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12940 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12940 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12942 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12942

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12942
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12942 (61 / 100) 164 (17 / (100 * 12942)) (26 / (10 * 12942)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12942 (61 / 100) 164 (17 / (100 * 12942)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (225155601 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (34794561 / 25000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2197918487 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12942 / 12942 * (61 / 100)) ^ 4 * inverseRadius8 (12942 - 1) /
            envelopeGap 12942 (61 / 100) 164 (17 / (100 * 12942)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12942

namespace BstLean.Part266.Row12942
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12942 164 ≤ (437145801 / 100000000000000000)
  f1 : (tableEnvelope C).f1 12942 164 ≤ (182299029 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (10953909 / 31250000000000000)
  w0 : (tableEnvelope C).w0 12942 164 ≤ (86613467 / 5000000000000000000)
  w1 : (tableEnvelope C).w1 12942 164 ≤ (616238241 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12942 164 ≤ (450315461 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (225155601 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (225155601 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (34794561 / 25000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2197918487 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((453037 / 125000000) : ℝ) ≤ √(17 / (100 * 12942) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12942) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2122053727 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37306600489 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12942) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12942) ≤ (54636593 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12942) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12942 * (164 : ℝ) ^ 2 + 26 / (10 * 12942) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12942) : ℝ)) (tA 12942 * 164 ^ 2 + 26 / (10 * 12942)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((453037 / 125000000))) * ((225155601 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((453037 / 125000000)) ^ 3) * ((34794561 / 25000000000000000000000))) + ((2197918487 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((453037 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12942) : ℝ)) d.D d.V d.P (√(tA 12942) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((453037 / 125000000)) ^ 2 * (((2122053727 / 1000000000000000)) * ((37306600489 / 1000000000000000000)))) + ((2197918487 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12942) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((453037 / 125000000)) * ((225155601 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12942) : ℝ)) (tA 12942 * 164 ^ 2 + 26 / (10 * 12942)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((225155601 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((453037 / 125000000)) ^ 2) * ((34794561 / 25000000000000000000000)) + ((2197918487 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12942) : ℝ)) (√(26 / (10 * 12942) : ℝ)) d.D d.V d.P (√(tA 12942) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((453037 / 125000000)) * (((2122053727 / 1000000000000000)) * ((37306600489 / 1000000000000000000))) + ((2197918487 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12942) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((225155601 / 50000000000000000000) : ℝ) + ((2197918487 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12942

namespace BstLean.Part266.Row12942
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12942 164 ∧
    0 ≤ (tableEnvelope C).f1 12942 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12942 164 ∧
    0 ≤ (tableEnvelope C).w1 12942 164 ∧ 0 ≤ (tableEnvelope C).w2 12942 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12942 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12942 164 ∧ 0 ≤ d.f1 12942 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12942 164 ∧ 0 ≤ d.w1 12942 164 ∧ 0 ≤ d.w2 12942 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12942 ≤ 2 * (228 / 100 : ℝ) / 12942 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12942 ≤ 2 * (370 / 100 : ℝ) / 12942 := by
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
    (completeRAData (tableEnvelope C) 12942 164).locationBound 12942 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12942 164).energyBound 12942 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12942 164) (d.f1 12942 164) d.f2 ≤
      32 * (((437145801 / 100000000000000000) : ℝ) + (182299029 / 125000000000000000) + (10953909 / 31250000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12942 164) (d.w1 12942 164)
      (d.w2 12942 164) ≤
      32 * (((86613467 / 5000000000000000000) : ℝ) + (616238241 / 50000000000000000000) + (450315461 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12942 164) (d.f1 12942 164) d.f2 ≤
      ((437145801 / 100000000000000000) : ℝ) ^ 2 + 2 * ((437145801 / 100000000000000000)) * ((182299029 / 125000000000000000)) * (126 / 100) +
      2 * (((182299029 / 125000000000000000)) ^ 2 + 2 * ((437145801 / 100000000000000000)) * ((10953909 / 31250000000000000))) +
      6 * ((182299029 / 125000000000000000)) * ((10953909 / 31250000000000000)) * (126 / 100) + 8 * ((10953909 / 31250000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12942 164) (d.f1 12942 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12942 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12942 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12942 164) (d.f1 12942 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12942 164) (d.w1 12942 164) (d.w2 12942 164)
  have hwexpr0 : 0 ≤ d.w0 12942 164 + d.w1 12942 164 * √(π / 2) +
      2 * d.w2 12942 164 + energyR16 12942 *
      radiusPolynomialRoot16 (d.w0 12942 164) (d.w1 12942 164) (d.w2 12942 164) := by
    positivity
  constructor
  · change (12942 : ℝ) ^ 8 * (mA 12942 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12942 164) (d.f1 12942 164) d.f2 + locationR16 12942 *
        radiusPolynomialRoot16 (d.f0 12942 164) (d.f1 12942 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12942 : ℝ) ^ 8 * (mA 12942 : ℝ) ^ 8 *
        ((((437145801 / 100000000000000000) : ℝ) ^ 2 + 2 * ((437145801 / 100000000000000000)) * ((182299029 / 125000000000000000)) * (126 / 100) +
          2 * (((182299029 / 125000000000000000)) ^ 2 + 2 * ((437145801 / 100000000000000000)) * ((10953909 / 31250000000000000))) +
          6 * ((182299029 / 125000000000000000)) * ((10953909 / 31250000000000000)) * (126 / 100) + 8 * ((10953909 / 31250000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12942) *
          (32 * (((437145801 / 100000000000000000) : ℝ) + (182299029 / 125000000000000000) + (10953909 / 31250000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12942 : ℝ) ^ 16 *
      (d.w0 12942 164 + d.w1 12942 164 * √(π / 2) + 2 * d.w2 12942 164 +
        energyR16 12942 * radiusPolynomialRoot16 (d.w0 12942 164) (d.w1 12942 164)
          (d.w2 12942 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12942 : ℝ) ^ 16 *
        (((86613467 / 5000000000000000000) : ℝ) + ((616238241 / 50000000000000000000)) * (126 / 100) + 2 * ((450315461 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12942) *
          (32 * (((86613467 / 5000000000000000000) : ℝ) + (616238241 / 50000000000000000000) + (450315461 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12942

/-! A coarse bound on the actual paper statistics constant at dimension 12943. -/
namespace BstLean.Part266.Row12943
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12941 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12941 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12941 128 ≤ (13195 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13195 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12943) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12943 : ℕ))
    (by norm_num : (12943 : ℕ) ≤ 16384)
  have ht : paperTail256 12943 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12943 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12943 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12943 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12943 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12943 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12941 128 * √(2 / (12943 : ℝ)) *
      (√(12943 : ℝ) + paperT0 12943 + paperTail256 12943) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12943 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12943 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12943 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12941 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12941 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12943 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12943

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12943
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12943 (61 / 100) 164 (17 / (100 * 12943)) (26 / (10 * 12943)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12943 (61 / 100) 164 (17 / (100 * 12943)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (450206829 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (695676173 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2196547441 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12943 / 12943 * (61 / 100)) ^ 4 * inverseRadius8 (12943 - 1) /
            envelopeGap 12943 (61 / 100) 164 (17 / (100 * 12943)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12943

namespace BstLean.Part266.Row12943
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12943 164 ≤ (2185306797 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12943 164 ≤ (729055263 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (350457381 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12943 164 ≤ (865933913 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12943 164 ≤ (246438163 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12943 164 ≤ (90042217 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (450206829 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (450206829 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (695676173 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2196547441 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((906039 / 250000000) : ℝ) ≤ √(17 / (100 * 12943) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12943) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2121807789 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (2331302233 / 62500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12943) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12943) ≤ (109264743 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12943) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12943 * (164 : ℝ) ^ 2 + 26 / (10 * 12943) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12943) : ℝ)) (tA 12943 * 164 ^ 2 + 26 / (10 * 12943)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((906039 / 250000000))) * ((450206829 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((906039 / 250000000)) ^ 3) * ((695676173 / 500000000000000000000000))) + ((2196547441 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((906039 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12943) : ℝ)) d.D d.V d.P (√(tA 12943) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((906039 / 250000000)) ^ 2 * (((2121807789 / 1000000000000000)) * ((2331302233 / 62500000000000000)))) + ((2196547441 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12943) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((906039 / 250000000)) * ((450206829 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12943) : ℝ)) (tA 12943 * 164 ^ 2 + 26 / (10 * 12943)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((450206829 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((906039 / 250000000)) ^ 2) * ((695676173 / 500000000000000000000000)) + ((2196547441 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12943) : ℝ)) (√(26 / (10 * 12943) : ℝ)) d.D d.V d.P (√(tA 12943) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((906039 / 250000000)) * (((2121807789 / 1000000000000000)) * ((2331302233 / 62500000000000000))) + ((2196547441 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12943) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((450206829 / 100000000000000000000) : ℝ) + ((2196547441 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12943

namespace BstLean.Part266.Row12943
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12943 164 ∧
    0 ≤ (tableEnvelope C).f1 12943 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12943 164 ∧
    0 ≤ (tableEnvelope C).w1 12943 164 ∧ 0 ≤ (tableEnvelope C).w2 12943 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12943 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12943 164 ∧ 0 ≤ d.f1 12943 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12943 164 ∧ 0 ≤ d.w1 12943 164 ∧ 0 ≤ d.w2 12943 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12943 ≤ 2 * (228 / 100 : ℝ) / 12943 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12943 ≤ 2 * (370 / 100 : ℝ) / 12943 := by
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
    (completeRAData (tableEnvelope C) 12943 164).locationBound 12943 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12943 164).energyBound 12943 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12943 164) (d.f1 12943 164) d.f2 ≤
      32 * (((2185306797 / 500000000000000000) : ℝ) + (729055263 / 500000000000000000) + (350457381 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12943 164) (d.w1 12943 164)
      (d.w2 12943 164) ≤
      32 * (((865933913 / 50000000000000000000) : ℝ) + (246438163 / 20000000000000000000) + (90042217 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12943 164) (d.f1 12943 164) d.f2 ≤
      ((2185306797 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2185306797 / 500000000000000000)) * ((729055263 / 500000000000000000)) * (126 / 100) +
      2 * (((729055263 / 500000000000000000)) ^ 2 + 2 * ((2185306797 / 500000000000000000)) * ((350457381 / 1000000000000000000))) +
      6 * ((729055263 / 500000000000000000)) * ((350457381 / 1000000000000000000)) * (126 / 100) + 8 * ((350457381 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12943 164) (d.f1 12943 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12943 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12943 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12943 164) (d.f1 12943 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12943 164) (d.w1 12943 164) (d.w2 12943 164)
  have hwexpr0 : 0 ≤ d.w0 12943 164 + d.w1 12943 164 * √(π / 2) +
      2 * d.w2 12943 164 + energyR16 12943 *
      radiusPolynomialRoot16 (d.w0 12943 164) (d.w1 12943 164) (d.w2 12943 164) := by
    positivity
  constructor
  · change (12943 : ℝ) ^ 8 * (mA 12943 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12943 164) (d.f1 12943 164) d.f2 + locationR16 12943 *
        radiusPolynomialRoot16 (d.f0 12943 164) (d.f1 12943 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12943 : ℝ) ^ 8 * (mA 12943 : ℝ) ^ 8 *
        ((((2185306797 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2185306797 / 500000000000000000)) * ((729055263 / 500000000000000000)) * (126 / 100) +
          2 * (((729055263 / 500000000000000000)) ^ 2 + 2 * ((2185306797 / 500000000000000000)) * ((350457381 / 1000000000000000000))) +
          6 * ((729055263 / 500000000000000000)) * ((350457381 / 1000000000000000000)) * (126 / 100) + 8 * ((350457381 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12943) *
          (32 * (((2185306797 / 500000000000000000) : ℝ) + (729055263 / 500000000000000000) + (350457381 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12943 : ℝ) ^ 16 *
      (d.w0 12943 164 + d.w1 12943 164 * √(π / 2) + 2 * d.w2 12943 164 +
        energyR16 12943 * radiusPolynomialRoot16 (d.w0 12943 164) (d.w1 12943 164)
          (d.w2 12943 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12943 : ℝ) ^ 16 *
        (((865933913 / 50000000000000000000) : ℝ) + ((246438163 / 20000000000000000000)) * (126 / 100) + 2 * ((90042217 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12943) *
          (32 * (((865933913 / 50000000000000000000) : ℝ) + (246438163 / 20000000000000000000) + (90042217 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12943

/-! A coarse bound on the actual paper statistics constant at dimension 12944. -/
namespace BstLean.Part266.Row12944
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12942 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12942 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12942 128 ≤ (13196 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13196 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12944) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12944 : ℕ))
    (by norm_num : (12944 : ℕ) ≤ 16384)
  have ht : paperTail256 12944 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12944 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12944 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12944 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12944 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12944 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12942 128 * √(2 / (12944 : ℝ)) *
      (√(12944 : ℝ) + paperT0 12944 + paperTail256 12944) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12944 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12944 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12944 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12942 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12942 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12944 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12944

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12944
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12944 (61 / 100) 164 (17 / (100 * 12944)) (26 / (10 * 12944)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12944 (61 / 100) 164 (17 / (100 * 12944)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (450102489 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1390922419 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (878070943 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12944 / 12944 * (61 / 100)) ^ 4 * inverseRadius8 (12944 - 1) /
            envelopeGap 12944 (61 / 100) 164 (17 / (100 * 12944)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12944

namespace BstLean.Part266.Row12944
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12944 164 ≤ (873953893 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12944 164 ≤ (1457828909 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (175194847 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12944 164 ≤ (108216653 / 6250000000000000000)
  w1 : (tableEnvelope C).w1 12944 164 ≤ (615952621 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12944 164 ≤ (225053371 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (450102489 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (450102489 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1390922419 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (878070943 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((226501 / 62500000) : ℝ) ≤ √(17 / (100 * 12944) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12944) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2121561899 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9323768079 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12944) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12944) ≤ (54628151 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12944) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12944 * (164 : ℝ) ^ 2 + 26 / (10 * 12944) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12944) : ℝ)) (tA 12944 * 164 ^ 2 + 26 / (10 * 12944)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((226501 / 62500000))) * ((450102489 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((226501 / 62500000)) ^ 3) * ((1390922419 / 1000000000000000000000000))) + ((878070943 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((226501 / 62500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12944) : ℝ)) d.D d.V d.P (√(tA 12944) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((226501 / 62500000)) ^ 2 * (((2121561899 / 1000000000000000)) * ((9323768079 / 250000000000000000)))) + ((878070943 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12944) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((226501 / 62500000)) * ((450102489 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12944) : ℝ)) (tA 12944 * 164 ^ 2 + 26 / (10 * 12944)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((450102489 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((226501 / 62500000)) ^ 2) * ((1390922419 / 1000000000000000000000000)) + ((878070943 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12944) : ℝ)) (√(26 / (10 * 12944) : ℝ)) d.D d.V d.P (√(tA 12944) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((226501 / 62500000)) * (((2121561899 / 1000000000000000)) * ((9323768079 / 250000000000000000))) + ((878070943 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12944) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((450102489 / 100000000000000000000) : ℝ) + ((878070943 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12944

namespace BstLean.Part266.Row12944
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12944 164 ∧
    0 ≤ (tableEnvelope C).f1 12944 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12944 164 ∧
    0 ≤ (tableEnvelope C).w1 12944 164 ∧ 0 ≤ (tableEnvelope C).w2 12944 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12944 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12944 164 ∧ 0 ≤ d.f1 12944 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12944 164 ∧ 0 ≤ d.w1 12944 164 ∧ 0 ≤ d.w2 12944 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12944 ≤ 2 * (228 / 100 : ℝ) / 12944 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12944 ≤ 2 * (370 / 100 : ℝ) / 12944 := by
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
    (completeRAData (tableEnvelope C) 12944 164).locationBound 12944 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12944 164).energyBound 12944 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12944 164) (d.f1 12944 164) d.f2 ≤
      32 * (((873953893 / 200000000000000000) : ℝ) + (1457828909 / 1000000000000000000) + (175194847 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12944 164) (d.w1 12944 164)
      (d.w2 12944 164) ≤
      32 * (((108216653 / 6250000000000000000) : ℝ) + (615952621 / 50000000000000000000) + (225053371 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12944 164) (d.f1 12944 164) d.f2 ≤
      ((873953893 / 200000000000000000) : ℝ) ^ 2 + 2 * ((873953893 / 200000000000000000)) * ((1457828909 / 1000000000000000000)) * (126 / 100) +
      2 * (((1457828909 / 1000000000000000000)) ^ 2 + 2 * ((873953893 / 200000000000000000)) * ((175194847 / 500000000000000000))) +
      6 * ((1457828909 / 1000000000000000000)) * ((175194847 / 500000000000000000)) * (126 / 100) + 8 * ((175194847 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12944 164) (d.f1 12944 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12944 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12944 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12944 164) (d.f1 12944 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12944 164) (d.w1 12944 164) (d.w2 12944 164)
  have hwexpr0 : 0 ≤ d.w0 12944 164 + d.w1 12944 164 * √(π / 2) +
      2 * d.w2 12944 164 + energyR16 12944 *
      radiusPolynomialRoot16 (d.w0 12944 164) (d.w1 12944 164) (d.w2 12944 164) := by
    positivity
  constructor
  · change (12944 : ℝ) ^ 8 * (mA 12944 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12944 164) (d.f1 12944 164) d.f2 + locationR16 12944 *
        radiusPolynomialRoot16 (d.f0 12944 164) (d.f1 12944 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12944 : ℝ) ^ 8 * (mA 12944 : ℝ) ^ 8 *
        ((((873953893 / 200000000000000000) : ℝ) ^ 2 + 2 * ((873953893 / 200000000000000000)) * ((1457828909 / 1000000000000000000)) * (126 / 100) +
          2 * (((1457828909 / 1000000000000000000)) ^ 2 + 2 * ((873953893 / 200000000000000000)) * ((175194847 / 500000000000000000))) +
          6 * ((1457828909 / 1000000000000000000)) * ((175194847 / 500000000000000000)) * (126 / 100) + 8 * ((175194847 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12944) *
          (32 * (((873953893 / 200000000000000000) : ℝ) + (1457828909 / 1000000000000000000) + (175194847 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12944 : ℝ) ^ 16 *
      (d.w0 12944 164 + d.w1 12944 164 * √(π / 2) + 2 * d.w2 12944 164 +
        energyR16 12944 * radiusPolynomialRoot16 (d.w0 12944 164) (d.w1 12944 164)
          (d.w2 12944 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12944 : ℝ) ^ 16 *
        (((108216653 / 6250000000000000000) : ℝ) + ((615952621 / 50000000000000000000)) * (126 / 100) + 2 * ((225053371 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12944) *
          (32 * (((108216653 / 6250000000000000000) : ℝ) + (615952621 / 50000000000000000000) + (225053371 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12944

/-! A coarse bound on the actual paper statistics constant at dimension 12945. -/
namespace BstLean.Part266.Row12945
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12943 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12943 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12943 128 ≤ (13197 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13197 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12945) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12945 : ℕ))
    (by norm_num : (12945 : ℕ) ≤ 16384)
  have ht : paperTail256 12945 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12945 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12945 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12945 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12945 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12945 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12943 128 * √(2 / (12945 : ℝ)) *
      (√(12945 : ℝ) + paperT0 12945 + paperTail256 12945) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12945 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12945 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12945 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12943 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12943 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12945 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12945

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12945
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12945 (61 / 100) 164 (17 / (100 * 12945)) (26 / (10 * 12945)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12945 (61 / 100) 164 (17 / (100 * 12945)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (22499909 / 5000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (695246329 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4387616473 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12945 / 12945 * (61 / 100)) ^ 4 * inverseRadius8 (12945 - 1) /
            envelopeGap 12945 (61 / 100) 164 (17 / (100 * 12945)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12945

namespace BstLean.Part266.Row12945
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12945 164 ≤ (4368925621 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12945 164 ≤ (72877369 / 50000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (175161013 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12945 164 ≤ (346213041 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12945 164 ≤ (1231619761 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12945 164 ≤ (450002431 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (22499909 / 5000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (22499909 / 5000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (695246329 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4387616473 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((905969 / 250000000) : ℝ) ≤ √(17 / (100 * 12945) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12945) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1060658027 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18644655119 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12945) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12945) ≤ (54623931 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12945) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12945 * (164 : ℝ) ^ 2 + 26 / (10 * 12945) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12945) : ℝ)) (tA 12945 * 164 ^ 2 + 26 / (10 * 12945)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((905969 / 250000000))) * ((22499909 / 5000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((905969 / 250000000)) ^ 3) * ((695246329 / 500000000000000000000000))) + ((4387616473 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((905969 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12945) : ℝ)) d.D d.V d.P (√(tA 12945) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((905969 / 250000000)) ^ 2 * (((1060658027 / 500000000000000)) * ((18644655119 / 500000000000000000)))) + ((4387616473 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12945) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((905969 / 250000000)) * ((22499909 / 5000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12945) : ℝ)) (tA 12945 * 164 ^ 2 + 26 / (10 * 12945)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((22499909 / 5000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((905969 / 250000000)) ^ 2) * ((695246329 / 500000000000000000000000)) + ((4387616473 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12945) : ℝ)) (√(26 / (10 * 12945) : ℝ)) d.D d.V d.P (√(tA 12945) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((905969 / 250000000)) * (((1060658027 / 500000000000000)) * ((18644655119 / 500000000000000000))) + ((4387616473 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12945) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((22499909 / 5000000000000000000) : ℝ) + ((4387616473 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12945

namespace BstLean.Part266.Row12945
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12945 164 ∧
    0 ≤ (tableEnvelope C).f1 12945 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12945 164 ∧
    0 ≤ (tableEnvelope C).w1 12945 164 ∧ 0 ≤ (tableEnvelope C).w2 12945 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12945 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12945 164 ∧ 0 ≤ d.f1 12945 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12945 164 ∧ 0 ≤ d.w1 12945 164 ∧ 0 ≤ d.w2 12945 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12945 ≤ 2 * (228 / 100 : ℝ) / 12945 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12945 ≤ 2 * (370 / 100 : ℝ) / 12945 := by
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
    (completeRAData (tableEnvelope C) 12945 164).locationBound 12945 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12945 164).energyBound 12945 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12945 164) (d.f1 12945 164) d.f2 ≤
      32 * (((4368925621 / 1000000000000000000) : ℝ) + (72877369 / 50000000000000000) + (175161013 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12945 164) (d.w1 12945 164)
      (d.w2 12945 164) ≤
      32 * (((346213041 / 20000000000000000000) : ℝ) + (1231619761 / 100000000000000000000) + (450002431 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12945 164) (d.f1 12945 164) d.f2 ≤
      ((4368925621 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4368925621 / 1000000000000000000)) * ((72877369 / 50000000000000000)) * (126 / 100) +
      2 * (((72877369 / 50000000000000000)) ^ 2 + 2 * ((4368925621 / 1000000000000000000)) * ((175161013 / 500000000000000000))) +
      6 * ((72877369 / 50000000000000000)) * ((175161013 / 500000000000000000)) * (126 / 100) + 8 * ((175161013 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12945 164) (d.f1 12945 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12945 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12945 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12945 164) (d.f1 12945 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12945 164) (d.w1 12945 164) (d.w2 12945 164)
  have hwexpr0 : 0 ≤ d.w0 12945 164 + d.w1 12945 164 * √(π / 2) +
      2 * d.w2 12945 164 + energyR16 12945 *
      radiusPolynomialRoot16 (d.w0 12945 164) (d.w1 12945 164) (d.w2 12945 164) := by
    positivity
  constructor
  · change (12945 : ℝ) ^ 8 * (mA 12945 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12945 164) (d.f1 12945 164) d.f2 + locationR16 12945 *
        radiusPolynomialRoot16 (d.f0 12945 164) (d.f1 12945 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12945 : ℝ) ^ 8 * (mA 12945 : ℝ) ^ 8 *
        ((((4368925621 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4368925621 / 1000000000000000000)) * ((72877369 / 50000000000000000)) * (126 / 100) +
          2 * (((72877369 / 50000000000000000)) ^ 2 + 2 * ((4368925621 / 1000000000000000000)) * ((175161013 / 500000000000000000))) +
          6 * ((72877369 / 50000000000000000)) * ((175161013 / 500000000000000000)) * (126 / 100) + 8 * ((175161013 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12945) *
          (32 * (((4368925621 / 1000000000000000000) : ℝ) + (72877369 / 50000000000000000) + (175161013 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12945 : ℝ) ^ 16 *
      (d.w0 12945 164 + d.w1 12945 164 * √(π / 2) + 2 * d.w2 12945 164 +
        energyR16 12945 * radiusPolynomialRoot16 (d.w0 12945 164) (d.w1 12945 164)
          (d.w2 12945 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12945 : ℝ) ^ 16 *
        (((346213041 / 20000000000000000000) : ℝ) + ((1231619761 / 100000000000000000000)) * (126 / 100) + 2 * ((450002431 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12945) *
          (32 * (((346213041 / 20000000000000000000) : ℝ) + (1231619761 / 100000000000000000000) + (450002431 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12945

/-! A coarse bound on the actual paper statistics constant at dimension 12946. -/
namespace BstLean.Part266.Row12946
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12944 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12944 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12944 128 ≤ (13198 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13198 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12946) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12946 : ℕ))
    (by norm_num : (12946 : ℕ) ≤ 16384)
  have ht : paperTail256 12946 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12946 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12946 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12946 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12946 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12946 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12944 128 * √(2 / (12946 : ℝ)) *
      (√(12946 : ℝ) + paperT0 12946 + paperTail256 12946) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12946 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12946 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12946 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12944 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12944 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12946 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12946

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12946
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12946 (61 / 100) 164 (17 / (100 * 12946)) (26 / (10 * 12946)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12946 (61 / 100) 164 (17 / (100 * 12946)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (28118369 / 6250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (695031531 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (876976031 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12946 / 12946 * (61 / 100)) ^ 4 * inverseRadius8 (12946 - 1) /
            envelopeGap 12946 (61 / 100) 164 (17 / (100 * 12946)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12946

namespace BstLean.Part266.Row12946
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12946 164 ≤ (4368082059 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12946 164 ≤ (728632971 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (350254379 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12946 164 ≤ (1730664097 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12946 164 ≤ (153916797 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 12946 164 ≤ (56237269 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (28118369 / 6250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (28118369 / 6250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (695031531 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (876976031 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((452967 / 125000000) : ℝ) ≤ √(17 / (100 * 12946) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12946) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2121070259 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37283549483 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12946) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12946) ≤ (109239423 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12946) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12946 * (164 : ℝ) ^ 2 + 26 / (10 * 12946) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12946) : ℝ)) (tA 12946 * 164 ^ 2 + 26 / (10 * 12946)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((452967 / 125000000))) * ((28118369 / 6250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((452967 / 125000000)) ^ 3) * ((695031531 / 500000000000000000000000))) + ((876976031 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((452967 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12946) : ℝ)) d.D d.V d.P (√(tA 12946) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((452967 / 125000000)) ^ 2 * (((2121070259 / 1000000000000000)) * ((37283549483 / 1000000000000000000)))) + ((876976031 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12946) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((452967 / 125000000)) * ((28118369 / 6250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12946) : ℝ)) (tA 12946 * 164 ^ 2 + 26 / (10 * 12946)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((28118369 / 6250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((452967 / 125000000)) ^ 2) * ((695031531 / 500000000000000000000000)) + ((876976031 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12946) : ℝ)) (√(26 / (10 * 12946) : ℝ)) d.D d.V d.P (√(tA 12946) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((452967 / 125000000)) * (((2121070259 / 1000000000000000)) * ((37283549483 / 1000000000000000000))) + ((876976031 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12946) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((28118369 / 6250000000000000000) : ℝ) + ((876976031 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12946

namespace BstLean.Part266.Row12946
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12946 164 ∧
    0 ≤ (tableEnvelope C).f1 12946 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12946 164 ∧
    0 ≤ (tableEnvelope C).w1 12946 164 ∧ 0 ≤ (tableEnvelope C).w2 12946 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12946 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12946 164 ∧ 0 ≤ d.f1 12946 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12946 164 ∧ 0 ≤ d.w1 12946 164 ∧ 0 ≤ d.w2 12946 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12946 ≤ 2 * (228 / 100 : ℝ) / 12946 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12946 ≤ 2 * (370 / 100 : ℝ) / 12946 := by
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
    (completeRAData (tableEnvelope C) 12946 164).locationBound 12946 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12946 164).energyBound 12946 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12946 164) (d.f1 12946 164) d.f2 ≤
      32 * (((4368082059 / 1000000000000000000) : ℝ) + (728632971 / 500000000000000000) + (350254379 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12946 164) (d.w1 12946 164)
      (d.w2 12946 164) ≤
      32 * (((1730664097 / 100000000000000000000) : ℝ) + (153916797 / 12500000000000000000) + (56237269 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12946 164) (d.f1 12946 164) d.f2 ≤
      ((4368082059 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4368082059 / 1000000000000000000)) * ((728632971 / 500000000000000000)) * (126 / 100) +
      2 * (((728632971 / 500000000000000000)) ^ 2 + 2 * ((4368082059 / 1000000000000000000)) * ((350254379 / 1000000000000000000))) +
      6 * ((728632971 / 500000000000000000)) * ((350254379 / 1000000000000000000)) * (126 / 100) + 8 * ((350254379 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12946 164) (d.f1 12946 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12946 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12946 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12946 164) (d.f1 12946 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12946 164) (d.w1 12946 164) (d.w2 12946 164)
  have hwexpr0 : 0 ≤ d.w0 12946 164 + d.w1 12946 164 * √(π / 2) +
      2 * d.w2 12946 164 + energyR16 12946 *
      radiusPolynomialRoot16 (d.w0 12946 164) (d.w1 12946 164) (d.w2 12946 164) := by
    positivity
  constructor
  · change (12946 : ℝ) ^ 8 * (mA 12946 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12946 164) (d.f1 12946 164) d.f2 + locationR16 12946 *
        radiusPolynomialRoot16 (d.f0 12946 164) (d.f1 12946 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12946 : ℝ) ^ 8 * (mA 12946 : ℝ) ^ 8 *
        ((((4368082059 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4368082059 / 1000000000000000000)) * ((728632971 / 500000000000000000)) * (126 / 100) +
          2 * (((728632971 / 500000000000000000)) ^ 2 + 2 * ((4368082059 / 1000000000000000000)) * ((350254379 / 1000000000000000000))) +
          6 * ((728632971 / 500000000000000000)) * ((350254379 / 1000000000000000000)) * (126 / 100) + 8 * ((350254379 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12946) *
          (32 * (((4368082059 / 1000000000000000000) : ℝ) + (728632971 / 500000000000000000) + (350254379 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12946 : ℝ) ^ 16 *
      (d.w0 12946 164 + d.w1 12946 164 * √(π / 2) + 2 * d.w2 12946 164 +
        energyR16 12946 * radiusPolynomialRoot16 (d.w0 12946 164) (d.w1 12946 164)
          (d.w2 12946 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12946 : ℝ) ^ 16 *
        (((1730664097 / 100000000000000000000) : ℝ) + ((153916797 / 12500000000000000000)) * (126 / 100) + 2 * ((56237269 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12946) *
          (32 * (((1730664097 / 100000000000000000000) : ℝ) + (153916797 / 12500000000000000000) + (56237269 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12946

/-! A coarse bound on the actual paper statistics constant at dimension 12947. -/
namespace BstLean.Part266.Row12947
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12945 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12945 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12945 128 ≤ (13199 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13199 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12947) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12947 : ℕ))
    (by norm_num : (12947 : ℕ) ≤ 16384)
  have ht : paperTail256 12947 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12947 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12947 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12947 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12947 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12947 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12945 128 * √(2 / (12947 : ℝ)) *
      (√(12947 : ℝ) + paperT0 12947 + paperTail256 12947) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12947 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12947 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12947 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12945 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12945 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12947 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12947

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12947
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12947 (61 / 100) 164 (17 / (100 * 12947)) (26 / (10 * 12947)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12947 (61 / 100) 164 (17 / (100 * 12947)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (22489483 / 5000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1389633633 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2191072879 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12947 / 12947 * (61 / 100)) ^ 4 * inverseRadius8 (12947 - 1) /
            envelopeGap 12947 (61 / 100) 164 (17 / (100 * 12947)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12947

namespace BstLean.Part266.Row12947
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12947 164 ≤ (34119053 / 7812500000000000)
  f1 : (tableEnvelope C).f1 12947 164 ≤ (91061537 / 62500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (1367917 / 3906250000000000)
  w0 : (tableEnvelope C).w0 12947 164 ≤ (865131563 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12947 164 ≤ (1231049083 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12947 164 ≤ (89958781 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (22489483 / 5000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (22489483 / 5000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1389633633 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2191072879 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((905899 / 250000000) : ℝ) ≤ √(17 / (100 * 12947) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12947) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (212082451 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37277790077 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12947) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12947) ≤ (21846197 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12947) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12947 * (164 : ℝ) ^ 2 + 26 / (10 * 12947) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12947) : ℝ)) (tA 12947 * 164 ^ 2 + 26 / (10 * 12947)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((905899 / 250000000))) * ((22489483 / 5000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((905899 / 250000000)) ^ 3) * ((1389633633 / 1000000000000000000000000))) + ((2191072879 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((905899 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12947) : ℝ)) d.D d.V d.P (√(tA 12947) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((905899 / 250000000)) ^ 2 * (((212082451 / 100000000000000)) * ((37277790077 / 1000000000000000000)))) + ((2191072879 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12947) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((905899 / 250000000)) * ((22489483 / 5000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12947) : ℝ)) (tA 12947 * 164 ^ 2 + 26 / (10 * 12947)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((22489483 / 5000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((905899 / 250000000)) ^ 2) * ((1389633633 / 1000000000000000000000000)) + ((2191072879 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12947) : ℝ)) (√(26 / (10 * 12947) : ℝ)) d.D d.V d.P (√(tA 12947) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((905899 / 250000000)) * (((212082451 / 100000000000000)) * ((37277790077 / 1000000000000000000))) + ((2191072879 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12947) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((22489483 / 5000000000000000000) : ℝ) + ((2191072879 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12947

namespace BstLean.Part266.Row12947
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12947 164 ∧
    0 ≤ (tableEnvelope C).f1 12947 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12947 164 ∧
    0 ≤ (tableEnvelope C).w1 12947 164 ∧ 0 ≤ (tableEnvelope C).w2 12947 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12947 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12947 164 ∧ 0 ≤ d.f1 12947 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12947 164 ∧ 0 ≤ d.w1 12947 164 ∧ 0 ≤ d.w2 12947 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12947 ≤ 2 * (228 / 100 : ℝ) / 12947 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12947 ≤ 2 * (370 / 100 : ℝ) / 12947 := by
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
    (completeRAData (tableEnvelope C) 12947 164).locationBound 12947 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12947 164).energyBound 12947 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12947 164) (d.f1 12947 164) d.f2 ≤
      32 * (((34119053 / 7812500000000000) : ℝ) + (91061537 / 62500000000000000) + (1367917 / 3906250000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12947 164) (d.w1 12947 164)
      (d.w2 12947 164) ≤
      32 * (((865131563 / 50000000000000000000) : ℝ) + (1231049083 / 100000000000000000000) + (89958781 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12947 164) (d.f1 12947 164) d.f2 ≤
      ((34119053 / 7812500000000000) : ℝ) ^ 2 + 2 * ((34119053 / 7812500000000000)) * ((91061537 / 62500000000000000)) * (126 / 100) +
      2 * (((91061537 / 62500000000000000)) ^ 2 + 2 * ((34119053 / 7812500000000000)) * ((1367917 / 3906250000000000))) +
      6 * ((91061537 / 62500000000000000)) * ((1367917 / 3906250000000000)) * (126 / 100) + 8 * ((1367917 / 3906250000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12947 164) (d.f1 12947 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12947 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12947 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12947 164) (d.f1 12947 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12947 164) (d.w1 12947 164) (d.w2 12947 164)
  have hwexpr0 : 0 ≤ d.w0 12947 164 + d.w1 12947 164 * √(π / 2) +
      2 * d.w2 12947 164 + energyR16 12947 *
      radiusPolynomialRoot16 (d.w0 12947 164) (d.w1 12947 164) (d.w2 12947 164) := by
    positivity
  constructor
  · change (12947 : ℝ) ^ 8 * (mA 12947 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12947 164) (d.f1 12947 164) d.f2 + locationR16 12947 *
        radiusPolynomialRoot16 (d.f0 12947 164) (d.f1 12947 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12947 : ℝ) ^ 8 * (mA 12947 : ℝ) ^ 8 *
        ((((34119053 / 7812500000000000) : ℝ) ^ 2 + 2 * ((34119053 / 7812500000000000)) * ((91061537 / 62500000000000000)) * (126 / 100) +
          2 * (((91061537 / 62500000000000000)) ^ 2 + 2 * ((34119053 / 7812500000000000)) * ((1367917 / 3906250000000000))) +
          6 * ((91061537 / 62500000000000000)) * ((1367917 / 3906250000000000)) * (126 / 100) + 8 * ((1367917 / 3906250000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12947) *
          (32 * (((34119053 / 7812500000000000) : ℝ) + (91061537 / 62500000000000000) + (1367917 / 3906250000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12947 : ℝ) ^ 16 *
      (d.w0 12947 164 + d.w1 12947 164 * √(π / 2) + 2 * d.w2 12947 164 +
        energyR16 12947 * radiusPolynomialRoot16 (d.w0 12947 164) (d.w1 12947 164)
          (d.w2 12947 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12947 : ℝ) ^ 16 *
        (((865131563 / 50000000000000000000) : ℝ) + ((1231049083 / 100000000000000000000)) * (126 / 100) + 2 * ((89958781 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12947) *
          (32 * (((865131563 / 50000000000000000000) : ℝ) + (1231049083 / 100000000000000000000) + (89958781 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12947

/-! A coarse bound on the actual paper statistics constant at dimension 12948. -/
namespace BstLean.Part266.Row12948
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12946 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12946 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12946 128 ≤ (13200 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13200 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12948) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12948 : ℕ))
    (by norm_num : (12948 : ℕ) ≤ 16384)
  have ht : paperTail256 12948 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12948 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12948 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12948 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12948 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12948 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12946 128 * √(2 / (12948 : ℝ)) *
      (√(12948 : ℝ) + paperT0 12948 + paperTail256 12948) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12948 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12948 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12948 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12946 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12946 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12948 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12948

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12948
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12948 (61 / 100) 164 (17 / (100 * 12948)) (26 / (10 * 12948)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12948 (61 / 100) 164 (17 / (100 * 12948)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (56210681 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1389204369 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (27371333 / 6250000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12948 / 12948 * (61 / 100)) ^ 4 * inverseRadius8 (12948 - 1) /
            envelopeGap 12948 (61 / 100) 164 (17 / (100 * 12948)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12948

namespace BstLean.Part266.Row12948
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12948 164 ≤ (545799039 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12948 164 ≤ (728351263 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (350119047 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12948 164 ≤ (864930791 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12948 164 ≤ (153845443 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 12948 164 ≤ (449689691 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (56210681 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (56210681 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1389204369 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (27371333 / 6250000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3623457 / 1000000000) : ℝ) ≤ √(17 / (100 * 12948) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12948) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (265072351 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7454406399 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12948) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12948) ≤ (109222549 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12948) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12948 * (164 : ℝ) ^ 2 + 26 / (10 * 12948) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12948) : ℝ)) (tA 12948 * 164 ^ 2 + 26 / (10 * 12948)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3623457 / 1000000000))) * ((56210681 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3623457 / 1000000000)) ^ 3) * ((1389204369 / 1000000000000000000000000))) + ((27371333 / 6250000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3623457 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12948) : ℝ)) d.D d.V d.P (√(tA 12948) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3623457 / 1000000000)) ^ 2 * (((265072351 / 125000000000000)) * ((7454406399 / 200000000000000000)))) + ((27371333 / 6250000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12948) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3623457 / 1000000000)) * ((56210681 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12948) : ℝ)) (tA 12948 * 164 ^ 2 + 26 / (10 * 12948)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((56210681 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3623457 / 1000000000)) ^ 2) * ((1389204369 / 1000000000000000000000000)) + ((27371333 / 6250000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12948) : ℝ)) (√(26 / (10 * 12948) : ℝ)) d.D d.V d.P (√(tA 12948) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3623457 / 1000000000)) * (((265072351 / 125000000000000)) * ((7454406399 / 200000000000000000))) + ((27371333 / 6250000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12948) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((56210681 / 12500000000000000000) : ℝ) + ((27371333 / 6250000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12948

namespace BstLean.Part266.Row12948
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12948 164 ∧
    0 ≤ (tableEnvelope C).f1 12948 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12948 164 ∧
    0 ≤ (tableEnvelope C).w1 12948 164 ∧ 0 ≤ (tableEnvelope C).w2 12948 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12948 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12948 164 ∧ 0 ≤ d.f1 12948 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12948 164 ∧ 0 ≤ d.w1 12948 164 ∧ 0 ≤ d.w2 12948 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12948 ≤ 2 * (228 / 100 : ℝ) / 12948 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12948 ≤ 2 * (370 / 100 : ℝ) / 12948 := by
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
    (completeRAData (tableEnvelope C) 12948 164).locationBound 12948 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12948 164).energyBound 12948 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12948 164) (d.f1 12948 164) d.f2 ≤
      32 * (((545799039 / 125000000000000000) : ℝ) + (728351263 / 500000000000000000) + (350119047 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12948 164) (d.w1 12948 164)
      (d.w2 12948 164) ≤
      32 * (((864930791 / 50000000000000000000) : ℝ) + (153845443 / 12500000000000000000) + (449689691 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12948 164) (d.f1 12948 164) d.f2 ≤
      ((545799039 / 125000000000000000) : ℝ) ^ 2 + 2 * ((545799039 / 125000000000000000)) * ((728351263 / 500000000000000000)) * (126 / 100) +
      2 * (((728351263 / 500000000000000000)) ^ 2 + 2 * ((545799039 / 125000000000000000)) * ((350119047 / 1000000000000000000))) +
      6 * ((728351263 / 500000000000000000)) * ((350119047 / 1000000000000000000)) * (126 / 100) + 8 * ((350119047 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12948 164) (d.f1 12948 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12948 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12948 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12948 164) (d.f1 12948 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12948 164) (d.w1 12948 164) (d.w2 12948 164)
  have hwexpr0 : 0 ≤ d.w0 12948 164 + d.w1 12948 164 * √(π / 2) +
      2 * d.w2 12948 164 + energyR16 12948 *
      radiusPolynomialRoot16 (d.w0 12948 164) (d.w1 12948 164) (d.w2 12948 164) := by
    positivity
  constructor
  · change (12948 : ℝ) ^ 8 * (mA 12948 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12948 164) (d.f1 12948 164) d.f2 + locationR16 12948 *
        radiusPolynomialRoot16 (d.f0 12948 164) (d.f1 12948 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12948 : ℝ) ^ 8 * (mA 12948 : ℝ) ^ 8 *
        ((((545799039 / 125000000000000000) : ℝ) ^ 2 + 2 * ((545799039 / 125000000000000000)) * ((728351263 / 500000000000000000)) * (126 / 100) +
          2 * (((728351263 / 500000000000000000)) ^ 2 + 2 * ((545799039 / 125000000000000000)) * ((350119047 / 1000000000000000000))) +
          6 * ((728351263 / 500000000000000000)) * ((350119047 / 1000000000000000000)) * (126 / 100) + 8 * ((350119047 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12948) *
          (32 * (((545799039 / 125000000000000000) : ℝ) + (728351263 / 500000000000000000) + (350119047 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12948 : ℝ) ^ 16 *
      (d.w0 12948 164 + d.w1 12948 164 * √(π / 2) + 2 * d.w2 12948 164 +
        energyR16 12948 * radiusPolynomialRoot16 (d.w0 12948 164) (d.w1 12948 164)
          (d.w2 12948 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12948 : ℝ) ^ 16 *
        (((864930791 / 50000000000000000000) : ℝ) + ((153845443 / 12500000000000000000)) * (126 / 100) + 2 * ((449689691 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12948) *
          (32 * (((864930791 / 50000000000000000000) : ℝ) + (153845443 / 12500000000000000000) + (449689691 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12948

/-! A coarse bound on the actual paper statistics constant at dimension 12949. -/
namespace BstLean.Part266.Row12949
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12947 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12947 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12947 128 ≤ (13201 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13201 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12949) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12949 : ℕ))
    (by norm_num : (12949 : ℕ) ≤ 16384)
  have ht : paperTail256 12949 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12949 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12949 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12949 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12949 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12949 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12947 128 * √(2 / (12949 : ℝ)) *
      (√(12949 : ℝ) + paperT0 12949 + paperTail256 12949) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12949 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12949 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12949 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12947 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12947 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12949 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12949

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12949
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12949 (61 / 100) 164 (17 / (100 * 12949)) (26 / (10 * 12949)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12949 (61 / 100) 164 (17 / (100 * 12949)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (449581269 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1388775271 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2188341361 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12949 / 12949 * (61 / 100)) ^ 4 * inverseRadius8 (12949 - 1) /
            envelopeGap 12949 (61 / 100) 164 (17 / (100 * 12949)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12949

namespace BstLean.Part266.Row12949
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12949 164 ≤ (2182774803 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12949 164 ≤ (364105339 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (17502573 / 50000000000000000)
  w0 : (tableEnvelope C).w0 12949 164 ≤ (1729460881 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12949 164 ≤ (30761961 / 2500000000000000000)
  w2 : (tableEnvelope C).w2 12949 164 ≤ (449585509 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (449581269 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (449581269 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1388775271 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2188341361 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3623317 / 1000000000) : ℝ) ≤ √(17 / (100 * 12949) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12949) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (530083289 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (149065101 / 4000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12949) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12949) ≤ (21842823 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12949) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12949 * (164 : ℝ) ^ 2 + 26 / (10 * 12949) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12949) : ℝ)) (tA 12949 * 164 ^ 2 + 26 / (10 * 12949)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3623317 / 1000000000))) * ((449581269 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3623317 / 1000000000)) ^ 3) * ((1388775271 / 1000000000000000000000000))) + ((2188341361 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3623317 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12949) : ℝ)) d.D d.V d.P (√(tA 12949) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3623317 / 1000000000)) ^ 2 * (((530083289 / 250000000000000)) * ((149065101 / 4000000000000000)))) + ((2188341361 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12949) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3623317 / 1000000000)) * ((449581269 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12949) : ℝ)) (tA 12949 * 164 ^ 2 + 26 / (10 * 12949)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((449581269 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3623317 / 1000000000)) ^ 2) * ((1388775271 / 1000000000000000000000000)) + ((2188341361 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12949) : ℝ)) (√(26 / (10 * 12949) : ℝ)) d.D d.V d.P (√(tA 12949) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3623317 / 1000000000)) * (((530083289 / 250000000000000)) * ((149065101 / 4000000000000000))) + ((2188341361 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12949) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((449581269 / 100000000000000000000) : ℝ) + ((2188341361 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12949

namespace BstLean.Part266.Row12949
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12949 164 ∧
    0 ≤ (tableEnvelope C).f1 12949 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12949 164 ∧
    0 ≤ (tableEnvelope C).w1 12949 164 ∧ 0 ≤ (tableEnvelope C).w2 12949 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12949 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12949 164 ∧ 0 ≤ d.f1 12949 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12949 164 ∧ 0 ≤ d.w1 12949 164 ∧ 0 ≤ d.w2 12949 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12949 ≤ 2 * (228 / 100 : ℝ) / 12949 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12949 ≤ 2 * (370 / 100 : ℝ) / 12949 := by
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
    (completeRAData (tableEnvelope C) 12949 164).locationBound 12949 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12949 164).energyBound 12949 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12949 164) (d.f1 12949 164) d.f2 ≤
      32 * (((2182774803 / 500000000000000000) : ℝ) + (364105339 / 250000000000000000) + (17502573 / 50000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12949 164) (d.w1 12949 164)
      (d.w2 12949 164) ≤
      32 * (((1729460881 / 100000000000000000000) : ℝ) + (30761961 / 2500000000000000000) + (449585509 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12949 164) (d.f1 12949 164) d.f2 ≤
      ((2182774803 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2182774803 / 500000000000000000)) * ((364105339 / 250000000000000000)) * (126 / 100) +
      2 * (((364105339 / 250000000000000000)) ^ 2 + 2 * ((2182774803 / 500000000000000000)) * ((17502573 / 50000000000000000))) +
      6 * ((364105339 / 250000000000000000)) * ((17502573 / 50000000000000000)) * (126 / 100) + 8 * ((17502573 / 50000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12949 164) (d.f1 12949 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12949 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12949 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12949 164) (d.f1 12949 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12949 164) (d.w1 12949 164) (d.w2 12949 164)
  have hwexpr0 : 0 ≤ d.w0 12949 164 + d.w1 12949 164 * √(π / 2) +
      2 * d.w2 12949 164 + energyR16 12949 *
      radiusPolynomialRoot16 (d.w0 12949 164) (d.w1 12949 164) (d.w2 12949 164) := by
    positivity
  constructor
  · change (12949 : ℝ) ^ 8 * (mA 12949 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12949 164) (d.f1 12949 164) d.f2 + locationR16 12949 *
        radiusPolynomialRoot16 (d.f0 12949 164) (d.f1 12949 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12949 : ℝ) ^ 8 * (mA 12949 : ℝ) ^ 8 *
        ((((2182774803 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2182774803 / 500000000000000000)) * ((364105339 / 250000000000000000)) * (126 / 100) +
          2 * (((364105339 / 250000000000000000)) ^ 2 + 2 * ((2182774803 / 500000000000000000)) * ((17502573 / 50000000000000000))) +
          6 * ((364105339 / 250000000000000000)) * ((17502573 / 50000000000000000)) * (126 / 100) + 8 * ((17502573 / 50000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12949) *
          (32 * (((2182774803 / 500000000000000000) : ℝ) + (364105339 / 250000000000000000) + (17502573 / 50000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12949 : ℝ) ^ 16 *
      (d.w0 12949 164 + d.w1 12949 164 * √(π / 2) + 2 * d.w2 12949 164 +
        energyR16 12949 * radiusPolynomialRoot16 (d.w0 12949 164) (d.w1 12949 164)
          (d.w2 12949 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12949 : ℝ) ^ 16 *
        (((1729460881 / 100000000000000000000) : ℝ) + ((30761961 / 2500000000000000000)) * (126 / 100) + 2 * ((449585509 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12949) *
          (32 * (((1729460881 / 100000000000000000000) : ℝ) + (30761961 / 2500000000000000000) + (449585509 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12949
