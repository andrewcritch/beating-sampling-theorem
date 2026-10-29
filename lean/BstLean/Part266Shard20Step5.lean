import BstLean.Part266Shard20Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12850. -/
namespace BstLean.Part266.Row12850
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12848 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12848 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12848 128 ≤ (13102 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13102 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12850) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12850 : ℕ))
    (by norm_num : (12850 : ℕ) ≤ 16384)
  have ht : paperTail256 12850 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12850 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12850 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12850 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12850 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12850 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12848 128 * √(2 / (12850 : ℝ)) *
      (√(12850 : ℝ) + paperT0 12850 + paperTail256 12850) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12850 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12850 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12850 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12848 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12848 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12850 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12850

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12850
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12850 (61 / 100) 164 (17 / (100 * 12850)) (26 / (10 * 12850)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12850 (61 / 100) 164 (17 / (100 * 12850)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (230026589 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1432072169 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4656555239 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12850 / 12850 * (61 / 100)) ^ 4 * inverseRadius8 (12850 - 1) /
            envelopeGap 12850 (61 / 100) 164 (17 / (100 * 12850)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12850

namespace BstLean.Part266.Row12850
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12850 164 ≤ (4450127569 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12850 164 ≤ (1484637743 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (178416601 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12850 164 ≤ (176974507 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12850 164 ≤ (1259139747 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12850 164 ≤ (460057689 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (230026589 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (230026589 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1432072169 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4656555239 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3637247 / 1000000000) : ℝ) ≤ √(17 / (100 * 12850) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12850) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (536221257 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (591292647 / 15625000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12850) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12850) ≤ (110055531 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12850) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12850 * (164 : ℝ) ^ 2 + 26 / (10 * 12850) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12850) : ℝ)) (tA 12850 * 164 ^ 2 + 26 / (10 * 12850)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3637247 / 1000000000))) * ((230026589 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3637247 / 1000000000)) ^ 3) * ((1432072169 / 1000000000000000000000000))) + ((4656555239 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3637247 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12850) : ℝ)) d.D d.V d.P (√(tA 12850) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3637247 / 1000000000)) ^ 2 * (((536221257 / 250000000000000)) * ((591292647 / 15625000000000000)))) + ((4656555239 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12850) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3637247 / 1000000000)) * ((230026589 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12850) : ℝ)) (tA 12850 * 164 ^ 2 + 26 / (10 * 12850)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((230026589 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3637247 / 1000000000)) ^ 2) * ((1432072169 / 1000000000000000000000000)) + ((4656555239 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12850) : ℝ)) (√(26 / (10 * 12850) : ℝ)) d.D d.V d.P (√(tA 12850) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3637247 / 1000000000)) * (((536221257 / 250000000000000)) * ((591292647 / 15625000000000000))) + ((4656555239 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12850) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((230026589 / 50000000000000000000) : ℝ) + ((4656555239 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12850

namespace BstLean.Part266.Row12850
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12850 164 ∧
    0 ≤ (tableEnvelope C).f1 12850 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12850 164 ∧
    0 ≤ (tableEnvelope C).w1 12850 164 ∧ 0 ≤ (tableEnvelope C).w2 12850 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12850 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12850 164 ∧ 0 ≤ d.f1 12850 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12850 164 ∧ 0 ≤ d.w1 12850 164 ∧ 0 ≤ d.w2 12850 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12850 ≤ 2 * (228 / 100 : ℝ) / 12850 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12850 ≤ 2 * (370 / 100 : ℝ) / 12850 := by
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
    (completeRAData (tableEnvelope C) 12850 164).locationBound 12850 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12850 164).energyBound 12850 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12850 164) (d.f1 12850 164) d.f2 ≤
      32 * (((4450127569 / 1000000000000000000) : ℝ) + (1484637743 / 1000000000000000000) + (178416601 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12850 164) (d.w1 12850 164)
      (d.w2 12850 164) ≤
      32 * (((176974507 / 10000000000000000000) : ℝ) + (1259139747 / 100000000000000000000) + (460057689 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12850 164) (d.f1 12850 164) d.f2 ≤
      ((4450127569 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4450127569 / 1000000000000000000)) * ((1484637743 / 1000000000000000000)) * (126 / 100) +
      2 * (((1484637743 / 1000000000000000000)) ^ 2 + 2 * ((4450127569 / 1000000000000000000)) * ((178416601 / 500000000000000000))) +
      6 * ((1484637743 / 1000000000000000000)) * ((178416601 / 500000000000000000)) * (126 / 100) + 8 * ((178416601 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12850 164) (d.f1 12850 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12850 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12850 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12850 164) (d.f1 12850 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12850 164) (d.w1 12850 164) (d.w2 12850 164)
  have hwexpr0 : 0 ≤ d.w0 12850 164 + d.w1 12850 164 * √(π / 2) +
      2 * d.w2 12850 164 + energyR16 12850 *
      radiusPolynomialRoot16 (d.w0 12850 164) (d.w1 12850 164) (d.w2 12850 164) := by
    positivity
  constructor
  · change (12850 : ℝ) ^ 8 * (mA 12850 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12850 164) (d.f1 12850 164) d.f2 + locationR16 12850 *
        radiusPolynomialRoot16 (d.f0 12850 164) (d.f1 12850 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12850 : ℝ) ^ 8 * (mA 12850 : ℝ) ^ 8 *
        ((((4450127569 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4450127569 / 1000000000000000000)) * ((1484637743 / 1000000000000000000)) * (126 / 100) +
          2 * (((1484637743 / 1000000000000000000)) ^ 2 + 2 * ((4450127569 / 1000000000000000000)) * ((178416601 / 500000000000000000))) +
          6 * ((1484637743 / 1000000000000000000)) * ((178416601 / 500000000000000000)) * (126 / 100) + 8 * ((178416601 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12850) *
          (32 * (((4450127569 / 1000000000000000000) : ℝ) + (1484637743 / 1000000000000000000) + (178416601 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12850 : ℝ) ^ 16 *
      (d.w0 12850 164 + d.w1 12850 164 * √(π / 2) + 2 * d.w2 12850 164 +
        energyR16 12850 * radiusPolynomialRoot16 (d.w0 12850 164) (d.w1 12850 164)
          (d.w2 12850 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12850 : ℝ) ^ 16 *
        (((176974507 / 10000000000000000000) : ℝ) + ((1259139747 / 100000000000000000000)) * (126 / 100) + 2 * ((460057689 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12850) *
          (32 * (((176974507 / 10000000000000000000) : ℝ) + (1259139747 / 100000000000000000000) + (460057689 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12850

/-! A coarse bound on the actual paper statistics constant at dimension 12851. -/
namespace BstLean.Part266.Row12851
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12849 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12849 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12849 128 ≤ (13103 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13103 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12851) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12851 : ℕ))
    (by norm_num : (12851 : ℕ) ≤ 16384)
  have ht : paperTail256 12851 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12851 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12851 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12851 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12851 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12851 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12849 128 * √(2 / (12851 : ℝ)) *
      (√(12851 : ℝ) + paperT0 12851 + paperTail256 12851) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12851 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12851 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12851 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12849 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12849 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12851 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12851

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12851
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12851 (61 / 100) 164 (17 / (100 * 12851)) (26 / (10 * 12851)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12851 (61 / 100) 164 (17 / (100 * 12851)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (459945783 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1431626457 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (465362933 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12851 / 12851 * (61 / 100)) ^ 4 * inverseRadius8 (12851 - 1) /
            envelopeGap 12851 (61 / 100) 164 (17 / (100 * 12851)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12851

namespace BstLean.Part266.Row12851
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12851 164 ≤ (4449260017 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12851 164 ≤ (2968697 / 2000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (89190933 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12851 164 ≤ (110583223 / 6250000000000000000)
  w1 : (tableEnvelope C).w1 12851 164 ≤ (629422817 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12851 164 ≤ (459950291 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (459945783 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (459945783 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1431626457 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (465362933 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1818553 / 500000000) : ℝ) ≤ √(17 / (100 * 12851) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12851) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1072317331 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7567367989 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12851) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12851) ≤ (110046967 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12851) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12851 * (164 : ℝ) ^ 2 + 26 / (10 * 12851) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12851) : ℝ)) (tA 12851 * 164 ^ 2 + 26 / (10 * 12851)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1818553 / 500000000))) * ((459945783 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1818553 / 500000000)) ^ 3) * ((1431626457 / 1000000000000000000000000))) + ((465362933 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1818553 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12851) : ℝ)) d.D d.V d.P (√(tA 12851) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1818553 / 500000000)) ^ 2 * (((1072317331 / 500000000000000)) * ((7567367989 / 200000000000000000)))) + ((465362933 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12851) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1818553 / 500000000)) * ((459945783 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12851) : ℝ)) (tA 12851 * 164 ^ 2 + 26 / (10 * 12851)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((459945783 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1818553 / 500000000)) ^ 2) * ((1431626457 / 1000000000000000000000000)) + ((465362933 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12851) : ℝ)) (√(26 / (10 * 12851) : ℝ)) d.D d.V d.P (√(tA 12851) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1818553 / 500000000)) * (((1072317331 / 500000000000000)) * ((7567367989 / 200000000000000000))) + ((465362933 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12851) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((459945783 / 100000000000000000000) : ℝ) + ((465362933 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12851

namespace BstLean.Part266.Row12851
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12851 164 ∧
    0 ≤ (tableEnvelope C).f1 12851 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12851 164 ∧
    0 ≤ (tableEnvelope C).w1 12851 164 ∧ 0 ≤ (tableEnvelope C).w2 12851 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12851 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12851 164 ∧ 0 ≤ d.f1 12851 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12851 164 ∧ 0 ≤ d.w1 12851 164 ∧ 0 ≤ d.w2 12851 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12851 ≤ 2 * (228 / 100 : ℝ) / 12851 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12851 ≤ 2 * (370 / 100 : ℝ) / 12851 := by
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
    (completeRAData (tableEnvelope C) 12851 164).locationBound 12851 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12851 164).energyBound 12851 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12851 164) (d.f1 12851 164) d.f2 ≤
      32 * (((4449260017 / 1000000000000000000) : ℝ) + (2968697 / 2000000000000000) + (89190933 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12851 164) (d.w1 12851 164)
      (d.w2 12851 164) ≤
      32 * (((110583223 / 6250000000000000000) : ℝ) + (629422817 / 50000000000000000000) + (459950291 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12851 164) (d.f1 12851 164) d.f2 ≤
      ((4449260017 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4449260017 / 1000000000000000000)) * ((2968697 / 2000000000000000)) * (126 / 100) +
      2 * (((2968697 / 2000000000000000)) ^ 2 + 2 * ((4449260017 / 1000000000000000000)) * ((89190933 / 250000000000000000))) +
      6 * ((2968697 / 2000000000000000)) * ((89190933 / 250000000000000000)) * (126 / 100) + 8 * ((89190933 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12851 164) (d.f1 12851 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12851 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12851 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12851 164) (d.f1 12851 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12851 164) (d.w1 12851 164) (d.w2 12851 164)
  have hwexpr0 : 0 ≤ d.w0 12851 164 + d.w1 12851 164 * √(π / 2) +
      2 * d.w2 12851 164 + energyR16 12851 *
      radiusPolynomialRoot16 (d.w0 12851 164) (d.w1 12851 164) (d.w2 12851 164) := by
    positivity
  constructor
  · change (12851 : ℝ) ^ 8 * (mA 12851 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12851 164) (d.f1 12851 164) d.f2 + locationR16 12851 *
        radiusPolynomialRoot16 (d.f0 12851 164) (d.f1 12851 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12851 : ℝ) ^ 8 * (mA 12851 : ℝ) ^ 8 *
        ((((4449260017 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4449260017 / 1000000000000000000)) * ((2968697 / 2000000000000000)) * (126 / 100) +
          2 * (((2968697 / 2000000000000000)) ^ 2 + 2 * ((4449260017 / 1000000000000000000)) * ((89190933 / 250000000000000000))) +
          6 * ((2968697 / 2000000000000000)) * ((89190933 / 250000000000000000)) * (126 / 100) + 8 * ((89190933 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12851) *
          (32 * (((4449260017 / 1000000000000000000) : ℝ) + (2968697 / 2000000000000000) + (89190933 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12851 : ℝ) ^ 16 *
      (d.w0 12851 164 + d.w1 12851 164 * √(π / 2) + 2 * d.w2 12851 164 +
        energyR16 12851 * radiusPolynomialRoot16 (d.w0 12851 164) (d.w1 12851 164)
          (d.w2 12851 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12851 : ℝ) ^ 16 *
        (((110583223 / 6250000000000000000) : ℝ) + ((629422817 / 50000000000000000000)) * (126 / 100) + 2 * ((459950291 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12851) *
          (32 * (((110583223 / 6250000000000000000) : ℝ) + (629422817 / 50000000000000000000) + (459950291 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12851

/-! A coarse bound on the actual paper statistics constant at dimension 12852. -/
namespace BstLean.Part266.Row12852
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12850 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12850 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12850 128 ≤ (13104 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13104 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12852) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12852 : ℕ))
    (by norm_num : (12852 : ℕ) ≤ 16384)
  have ht : paperTail256 12852 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12852 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12852 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12852 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12852 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12852 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12850 128 * √(2 / (12852 : ℝ)) *
      (√(12852 : ℝ) + paperT0 12852 + paperTail256 12852) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12852 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12852 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12852 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12850 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12850 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12852 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12852

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12852
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12852 (61 / 100) 164 (17 / (100 * 12852)) (26 / (10 * 12852)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12852 (61 / 100) 164 (17 / (100 * 12852)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (459838423 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (715590459 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1162676373 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12852 / 12852 * (61 / 100)) ^ 4 * inverseRadius8 (12852 - 1) /
            envelopeGap 12852 (61 / 100) 164 (17 / (100 * 12852)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12852

namespace BstLean.Part266.Row12852
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12852 164 ≤ (4448396289 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12852 164 ≤ (1484060167 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (356694383 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12852 164 ≤ (1768918927 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12852 164 ≤ (629275983 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12852 164 ≤ (459842929 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (459838423 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (459838423 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (715590459 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1162676373 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((909241 / 250000000) : ℝ) ≤ √(17 / (100 * 12852) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12852) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (536096087 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9457737963 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12852) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12852) ≤ (27509601 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12852) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12852 * (164 : ℝ) ^ 2 + 26 / (10 * 12852) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12852) : ℝ)) (tA 12852 * 164 ^ 2 + 26 / (10 * 12852)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((909241 / 250000000))) * ((459838423 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((909241 / 250000000)) ^ 3) * ((715590459 / 500000000000000000000000))) + ((1162676373 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((909241 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12852) : ℝ)) d.D d.V d.P (√(tA 12852) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((909241 / 250000000)) ^ 2 * (((536096087 / 250000000000000)) * ((9457737963 / 250000000000000000)))) + ((1162676373 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12852) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((909241 / 250000000)) * ((459838423 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12852) : ℝ)) (tA 12852 * 164 ^ 2 + 26 / (10 * 12852)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((459838423 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((909241 / 250000000)) ^ 2) * ((715590459 / 500000000000000000000000)) + ((1162676373 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12852) : ℝ)) (√(26 / (10 * 12852) : ℝ)) d.D d.V d.P (√(tA 12852) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((909241 / 250000000)) * (((536096087 / 250000000000000)) * ((9457737963 / 250000000000000000))) + ((1162676373 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12852) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((459838423 / 100000000000000000000) : ℝ) + ((1162676373 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12852

namespace BstLean.Part266.Row12852
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12852 164 ∧
    0 ≤ (tableEnvelope C).f1 12852 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12852 164 ∧
    0 ≤ (tableEnvelope C).w1 12852 164 ∧ 0 ≤ (tableEnvelope C).w2 12852 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12852 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12852 164 ∧ 0 ≤ d.f1 12852 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12852 164 ∧ 0 ≤ d.w1 12852 164 ∧ 0 ≤ d.w2 12852 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12852 ≤ 2 * (228 / 100 : ℝ) / 12852 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12852 ≤ 2 * (370 / 100 : ℝ) / 12852 := by
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
    (completeRAData (tableEnvelope C) 12852 164).locationBound 12852 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12852 164).energyBound 12852 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12852 164) (d.f1 12852 164) d.f2 ≤
      32 * (((4448396289 / 1000000000000000000) : ℝ) + (1484060167 / 1000000000000000000) + (356694383 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12852 164) (d.w1 12852 164)
      (d.w2 12852 164) ≤
      32 * (((1768918927 / 100000000000000000000) : ℝ) + (629275983 / 50000000000000000000) + (459842929 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12852 164) (d.f1 12852 164) d.f2 ≤
      ((4448396289 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4448396289 / 1000000000000000000)) * ((1484060167 / 1000000000000000000)) * (126 / 100) +
      2 * (((1484060167 / 1000000000000000000)) ^ 2 + 2 * ((4448396289 / 1000000000000000000)) * ((356694383 / 1000000000000000000))) +
      6 * ((1484060167 / 1000000000000000000)) * ((356694383 / 1000000000000000000)) * (126 / 100) + 8 * ((356694383 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12852 164) (d.f1 12852 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12852 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12852 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12852 164) (d.f1 12852 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12852 164) (d.w1 12852 164) (d.w2 12852 164)
  have hwexpr0 : 0 ≤ d.w0 12852 164 + d.w1 12852 164 * √(π / 2) +
      2 * d.w2 12852 164 + energyR16 12852 *
      radiusPolynomialRoot16 (d.w0 12852 164) (d.w1 12852 164) (d.w2 12852 164) := by
    positivity
  constructor
  · change (12852 : ℝ) ^ 8 * (mA 12852 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12852 164) (d.f1 12852 164) d.f2 + locationR16 12852 *
        radiusPolynomialRoot16 (d.f0 12852 164) (d.f1 12852 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12852 : ℝ) ^ 8 * (mA 12852 : ℝ) ^ 8 *
        ((((4448396289 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4448396289 / 1000000000000000000)) * ((1484060167 / 1000000000000000000)) * (126 / 100) +
          2 * (((1484060167 / 1000000000000000000)) ^ 2 + 2 * ((4448396289 / 1000000000000000000)) * ((356694383 / 1000000000000000000))) +
          6 * ((1484060167 / 1000000000000000000)) * ((356694383 / 1000000000000000000)) * (126 / 100) + 8 * ((356694383 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12852) *
          (32 * (((4448396289 / 1000000000000000000) : ℝ) + (1484060167 / 1000000000000000000) + (356694383 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12852 : ℝ) ^ 16 *
      (d.w0 12852 164 + d.w1 12852 164 * √(π / 2) + 2 * d.w2 12852 164 +
        energyR16 12852 * radiusPolynomialRoot16 (d.w0 12852 164) (d.w1 12852 164)
          (d.w2 12852 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12852 : ℝ) ^ 16 *
        (((1768918927 / 100000000000000000000) : ℝ) + ((629275983 / 50000000000000000000)) * (126 / 100) + 2 * ((459842929 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12852) *
          (32 * (((1768918927 / 100000000000000000000) : ℝ) + (629275983 / 50000000000000000000) + (459842929 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12852

/-! A coarse bound on the actual paper statistics constant at dimension 12853. -/
namespace BstLean.Part266.Row12853
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12851 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12851 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12851 128 ≤ (13105 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13105 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12853) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12853 : ℕ))
    (by norm_num : (12853 : ℕ) ≤ 16384)
  have ht : paperTail256 12853 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12853 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12853 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12853 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12853 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12853 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12851 128 * √(2 / (12853 : ℝ)) *
      (√(12853 : ℝ) + paperT0 12853 + paperTail256 12853) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12853 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12853 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12853 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12851 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12851 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12853 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12853

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12853
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12853 (61 / 100) 164 (17 / (100 * 12853)) (26 / (10 * 12853)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12853 (61 / 100) 164 (17 / (100 * 12853)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (91946219 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1430735553 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4647783723 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12853 / 12853 * (61 / 100)) ^ 4 * inverseRadius8 (12853 - 1) /
            envelopeGap 12853 (61 / 100) 164 (17 / (100 * 12853)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12853

namespace BstLean.Part266.Row12853
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12853 164 ≤ (2223764663 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12853 164 ≤ (370942777 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (71324991 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12853 164 ≤ (1768505707 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12853 164 ≤ (9830141 / 781250000000000000)
  w2 : (tableEnvelope C).w2 12853 164 ≤ (229867799 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (91946219 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (91946219 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1430735553 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4647783723 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3636823 / 1000000000) : ℝ) ≤ √(17 / (100 * 12853) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12853) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (6700419 / 3125000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37825065143 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12853) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12853) ≤ (110029843 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12853) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12853 * (164 : ℝ) ^ 2 + 26 / (10 * 12853) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12853) : ℝ)) (tA 12853 * 164 ^ 2 + 26 / (10 * 12853)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3636823 / 1000000000))) * ((91946219 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3636823 / 1000000000)) ^ 3) * ((1430735553 / 1000000000000000000000000))) + ((4647783723 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3636823 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12853) : ℝ)) d.D d.V d.P (√(tA 12853) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3636823 / 1000000000)) ^ 2 * (((6700419 / 3125000000000)) * ((37825065143 / 1000000000000000000)))) + ((4647783723 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12853) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3636823 / 1000000000)) * ((91946219 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12853) : ℝ)) (tA 12853 * 164 ^ 2 + 26 / (10 * 12853)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((91946219 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3636823 / 1000000000)) ^ 2) * ((1430735553 / 1000000000000000000000000)) + ((4647783723 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12853) : ℝ)) (√(26 / (10 * 12853) : ℝ)) d.D d.V d.P (√(tA 12853) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3636823 / 1000000000)) * (((6700419 / 3125000000000)) * ((37825065143 / 1000000000000000000))) + ((4647783723 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12853) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((91946219 / 20000000000000000000) : ℝ) + ((4647783723 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12853

namespace BstLean.Part266.Row12853
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12853 164 ∧
    0 ≤ (tableEnvelope C).f1 12853 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12853 164 ∧
    0 ≤ (tableEnvelope C).w1 12853 164 ∧ 0 ≤ (tableEnvelope C).w2 12853 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12853 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12853 164 ∧ 0 ≤ d.f1 12853 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12853 164 ∧ 0 ≤ d.w1 12853 164 ∧ 0 ≤ d.w2 12853 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12853 ≤ 2 * (228 / 100 : ℝ) / 12853 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12853 ≤ 2 * (370 / 100 : ℝ) / 12853 := by
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
    (completeRAData (tableEnvelope C) 12853 164).locationBound 12853 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12853 164).energyBound 12853 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12853 164) (d.f1 12853 164) d.f2 ≤
      32 * (((2223764663 / 500000000000000000) : ℝ) + (370942777 / 250000000000000000) + (71324991 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12853 164) (d.w1 12853 164)
      (d.w2 12853 164) ≤
      32 * (((1768505707 / 100000000000000000000) : ℝ) + (9830141 / 781250000000000000) + (229867799 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12853 164) (d.f1 12853 164) d.f2 ≤
      ((2223764663 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2223764663 / 500000000000000000)) * ((370942777 / 250000000000000000)) * (126 / 100) +
      2 * (((370942777 / 250000000000000000)) ^ 2 + 2 * ((2223764663 / 500000000000000000)) * ((71324991 / 200000000000000000))) +
      6 * ((370942777 / 250000000000000000)) * ((71324991 / 200000000000000000)) * (126 / 100) + 8 * ((71324991 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12853 164) (d.f1 12853 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12853 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12853 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12853 164) (d.f1 12853 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12853 164) (d.w1 12853 164) (d.w2 12853 164)
  have hwexpr0 : 0 ≤ d.w0 12853 164 + d.w1 12853 164 * √(π / 2) +
      2 * d.w2 12853 164 + energyR16 12853 *
      radiusPolynomialRoot16 (d.w0 12853 164) (d.w1 12853 164) (d.w2 12853 164) := by
    positivity
  constructor
  · change (12853 : ℝ) ^ 8 * (mA 12853 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12853 164) (d.f1 12853 164) d.f2 + locationR16 12853 *
        radiusPolynomialRoot16 (d.f0 12853 164) (d.f1 12853 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12853 : ℝ) ^ 8 * (mA 12853 : ℝ) ^ 8 *
        ((((2223764663 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2223764663 / 500000000000000000)) * ((370942777 / 250000000000000000)) * (126 / 100) +
          2 * (((370942777 / 250000000000000000)) ^ 2 + 2 * ((2223764663 / 500000000000000000)) * ((71324991 / 200000000000000000))) +
          6 * ((370942777 / 250000000000000000)) * ((71324991 / 200000000000000000)) * (126 / 100) + 8 * ((71324991 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12853) *
          (32 * (((2223764663 / 500000000000000000) : ℝ) + (370942777 / 250000000000000000) + (71324991 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12853 : ℝ) ^ 16 *
      (d.w0 12853 164 + d.w1 12853 164 * √(π / 2) + 2 * d.w2 12853 164 +
        energyR16 12853 * radiusPolynomialRoot16 (d.w0 12853 164) (d.w1 12853 164)
          (d.w2 12853 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12853 : ℝ) ^ 16 *
        (((1768505707 / 100000000000000000000) : ℝ) + ((9830141 / 781250000000000000)) * (126 / 100) + 2 * ((229867799 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12853) *
          (32 * (((1768505707 / 100000000000000000000) : ℝ) + (9830141 / 781250000000000000) + (229867799 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12853

/-! A coarse bound on the actual paper statistics constant at dimension 12854. -/
namespace BstLean.Part266.Row12854
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12852 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12852 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12852 128 ≤ (13106 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13106 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12854) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12854 : ℕ))
    (by norm_num : (12854 : ℕ) ≤ 16384)
  have ht : paperTail256 12854 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12854 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12854 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12854 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12854 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12854 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12852 128 * √(2 / (12854 : ℝ)) *
      (√(12854 : ℝ) + paperT0 12854 + paperTail256 12854) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12854 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12854 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12854 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12852 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12852 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12854 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12854

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12854
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12854 (61 / 100) 164 (17 / (100 * 12854)) (26 / (10 * 12854)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12854 (61 / 100) 164 (17 / (100 * 12854)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (459623801 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1430290361 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (232243201 / 50000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12854 / 12854 * (61 / 100)) ^ 4 * inverseRadius8 (12854 - 1) /
            envelopeGap 12854 (61 / 100) 164 (17 / (100 * 12854)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12854

namespace BstLean.Part266.Row12854
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12854 164 ≤ (2223333093 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12854 164 ≤ (741741479 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (178277823 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12854 164 ≤ (1768093347 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12854 164 ≤ (628982287 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12854 164 ≤ (459628301 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (459623801 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (459623801 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1430290361 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (232243201 / 50000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3636681 / 1000000000) : ℝ) ≤ √(17 / (100 * 12854) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12854) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1071941931 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9454794951 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12854) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12854) ≤ (110021283 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12854) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12854 * (164 : ℝ) ^ 2 + 26 / (10 * 12854) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12854) : ℝ)) (tA 12854 * 164 ^ 2 + 26 / (10 * 12854)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3636681 / 1000000000))) * ((459623801 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3636681 / 1000000000)) ^ 3) * ((1430290361 / 1000000000000000000000000))) + ((232243201 / 50000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3636681 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12854) : ℝ)) d.D d.V d.P (√(tA 12854) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3636681 / 1000000000)) ^ 2 * (((1071941931 / 500000000000000)) * ((9454794951 / 250000000000000000)))) + ((232243201 / 50000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12854) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3636681 / 1000000000)) * ((459623801 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12854) : ℝ)) (tA 12854 * 164 ^ 2 + 26 / (10 * 12854)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((459623801 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3636681 / 1000000000)) ^ 2) * ((1430290361 / 1000000000000000000000000)) + ((232243201 / 50000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12854) : ℝ)) (√(26 / (10 * 12854) : ℝ)) d.D d.V d.P (√(tA 12854) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3636681 / 1000000000)) * (((1071941931 / 500000000000000)) * ((9454794951 / 250000000000000000))) + ((232243201 / 50000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12854) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((459623801 / 100000000000000000000) : ℝ) + ((232243201 / 50000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12854

namespace BstLean.Part266.Row12854
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12854 164 ∧
    0 ≤ (tableEnvelope C).f1 12854 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12854 164 ∧
    0 ≤ (tableEnvelope C).w1 12854 164 ∧ 0 ≤ (tableEnvelope C).w2 12854 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12854 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12854 164 ∧ 0 ≤ d.f1 12854 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12854 164 ∧ 0 ≤ d.w1 12854 164 ∧ 0 ≤ d.w2 12854 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12854 ≤ 2 * (228 / 100 : ℝ) / 12854 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12854 ≤ 2 * (370 / 100 : ℝ) / 12854 := by
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
    (completeRAData (tableEnvelope C) 12854 164).locationBound 12854 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12854 164).energyBound 12854 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12854 164) (d.f1 12854 164) d.f2 ≤
      32 * (((2223333093 / 500000000000000000) : ℝ) + (741741479 / 500000000000000000) + (178277823 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12854 164) (d.w1 12854 164)
      (d.w2 12854 164) ≤
      32 * (((1768093347 / 100000000000000000000) : ℝ) + (628982287 / 50000000000000000000) + (459628301 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12854 164) (d.f1 12854 164) d.f2 ≤
      ((2223333093 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2223333093 / 500000000000000000)) * ((741741479 / 500000000000000000)) * (126 / 100) +
      2 * (((741741479 / 500000000000000000)) ^ 2 + 2 * ((2223333093 / 500000000000000000)) * ((178277823 / 500000000000000000))) +
      6 * ((741741479 / 500000000000000000)) * ((178277823 / 500000000000000000)) * (126 / 100) + 8 * ((178277823 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12854 164) (d.f1 12854 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12854 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12854 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12854 164) (d.f1 12854 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12854 164) (d.w1 12854 164) (d.w2 12854 164)
  have hwexpr0 : 0 ≤ d.w0 12854 164 + d.w1 12854 164 * √(π / 2) +
      2 * d.w2 12854 164 + energyR16 12854 *
      radiusPolynomialRoot16 (d.w0 12854 164) (d.w1 12854 164) (d.w2 12854 164) := by
    positivity
  constructor
  · change (12854 : ℝ) ^ 8 * (mA 12854 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12854 164) (d.f1 12854 164) d.f2 + locationR16 12854 *
        radiusPolynomialRoot16 (d.f0 12854 164) (d.f1 12854 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12854 : ℝ) ^ 8 * (mA 12854 : ℝ) ^ 8 *
        ((((2223333093 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2223333093 / 500000000000000000)) * ((741741479 / 500000000000000000)) * (126 / 100) +
          2 * (((741741479 / 500000000000000000)) ^ 2 + 2 * ((2223333093 / 500000000000000000)) * ((178277823 / 500000000000000000))) +
          6 * ((741741479 / 500000000000000000)) * ((178277823 / 500000000000000000)) * (126 / 100) + 8 * ((178277823 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12854) *
          (32 * (((2223333093 / 500000000000000000) : ℝ) + (741741479 / 500000000000000000) + (178277823 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12854 : ℝ) ^ 16 *
      (d.w0 12854 164 + d.w1 12854 164 * √(π / 2) + 2 * d.w2 12854 164 +
        energyR16 12854 * radiusPolynomialRoot16 (d.w0 12854 164) (d.w1 12854 164)
          (d.w2 12854 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12854 : ℝ) ^ 16 *
        (((1768093347 / 100000000000000000000) : ℝ) + ((628982287 / 50000000000000000000)) * (126 / 100) + 2 * ((459628301 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12854) *
          (32 * (((1768093347 / 100000000000000000000) : ℝ) + (628982287 / 50000000000000000000) + (459628301 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12854

/-! A coarse bound on the actual paper statistics constant at dimension 12855. -/
namespace BstLean.Part266.Row12855
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12853 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12853 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12853 128 ≤ (13107 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13107 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12855) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12855 : ℕ))
    (by norm_num : (12855 : ℕ) ≤ 16384)
  have ht : paperTail256 12855 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12855 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12855 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12855 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12855 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12855 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12853 128 * √(2 / (12855 : ℝ)) *
      (√(12855 : ℝ) + paperT0 12855 + paperTail256 12855) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12855 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12855 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12855 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12853 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12853 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12855 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12855

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12855
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12855 (61 / 100) 164 (17 / (100 * 12855)) (26 / (10 * 12855)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12855 (61 / 100) 164 (17 / (100 * 12855)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (459516541 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1429845343 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4641946383 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12855 / 12855 * (61 / 100)) ^ 4 * inverseRadius8 (12855 - 1) /
            envelopeGap 12855 (61 / 100) 164 (17 / (100 * 12855)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12855

namespace BstLean.Part266.Row12855
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12855 164 ≤ (4445799813 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12855 164 ≤ (741597043 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (17824313 / 50000000000000000)
  w0 : (tableEnvelope C).w0 12855 164 ≤ (1767680409 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12855 164 ≤ (314417713 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12855 164 ≤ (229760519 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (459516541 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (459516541 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1429845343 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4641946383 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((181827 / 50000000) : ℝ) ≤ √(17 / (100 * 12855) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12855) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1071816847 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (756265917 / 20000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12855) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12855) ≤ (27503181 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12855) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12855 * (164 : ℝ) ^ 2 + 26 / (10 * 12855) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12855) : ℝ)) (tA 12855 * 164 ^ 2 + 26 / (10 * 12855)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((181827 / 50000000))) * ((459516541 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((181827 / 50000000)) ^ 3) * ((1429845343 / 1000000000000000000000000))) + ((4641946383 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((181827 / 50000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12855) : ℝ)) d.D d.V d.P (√(tA 12855) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((181827 / 50000000)) ^ 2 * (((1071816847 / 500000000000000)) * ((756265917 / 20000000000000000)))) + ((4641946383 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12855) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((181827 / 50000000)) * ((459516541 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12855) : ℝ)) (tA 12855 * 164 ^ 2 + 26 / (10 * 12855)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((459516541 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((181827 / 50000000)) ^ 2) * ((1429845343 / 1000000000000000000000000)) + ((4641946383 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12855) : ℝ)) (√(26 / (10 * 12855) : ℝ)) d.D d.V d.P (√(tA 12855) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((181827 / 50000000)) * (((1071816847 / 500000000000000)) * ((756265917 / 20000000000000000))) + ((4641946383 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12855) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((459516541 / 100000000000000000000) : ℝ) + ((4641946383 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12855

namespace BstLean.Part266.Row12855
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12855 164 ∧
    0 ≤ (tableEnvelope C).f1 12855 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12855 164 ∧
    0 ≤ (tableEnvelope C).w1 12855 164 ∧ 0 ≤ (tableEnvelope C).w2 12855 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12855 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12855 164 ∧ 0 ≤ d.f1 12855 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12855 164 ∧ 0 ≤ d.w1 12855 164 ∧ 0 ≤ d.w2 12855 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12855 ≤ 2 * (228 / 100 : ℝ) / 12855 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12855 ≤ 2 * (370 / 100 : ℝ) / 12855 := by
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
    (completeRAData (tableEnvelope C) 12855 164).locationBound 12855 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12855 164).energyBound 12855 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12855 164) (d.f1 12855 164) d.f2 ≤
      32 * (((4445799813 / 1000000000000000000) : ℝ) + (741597043 / 500000000000000000) + (17824313 / 50000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12855 164) (d.w1 12855 164)
      (d.w2 12855 164) ≤
      32 * (((1767680409 / 100000000000000000000) : ℝ) + (314417713 / 25000000000000000000) + (229760519 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12855 164) (d.f1 12855 164) d.f2 ≤
      ((4445799813 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4445799813 / 1000000000000000000)) * ((741597043 / 500000000000000000)) * (126 / 100) +
      2 * (((741597043 / 500000000000000000)) ^ 2 + 2 * ((4445799813 / 1000000000000000000)) * ((17824313 / 50000000000000000))) +
      6 * ((741597043 / 500000000000000000)) * ((17824313 / 50000000000000000)) * (126 / 100) + 8 * ((17824313 / 50000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12855 164) (d.f1 12855 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12855 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12855 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12855 164) (d.f1 12855 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12855 164) (d.w1 12855 164) (d.w2 12855 164)
  have hwexpr0 : 0 ≤ d.w0 12855 164 + d.w1 12855 164 * √(π / 2) +
      2 * d.w2 12855 164 + energyR16 12855 *
      radiusPolynomialRoot16 (d.w0 12855 164) (d.w1 12855 164) (d.w2 12855 164) := by
    positivity
  constructor
  · change (12855 : ℝ) ^ 8 * (mA 12855 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12855 164) (d.f1 12855 164) d.f2 + locationR16 12855 *
        radiusPolynomialRoot16 (d.f0 12855 164) (d.f1 12855 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12855 : ℝ) ^ 8 * (mA 12855 : ℝ) ^ 8 *
        ((((4445799813 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4445799813 / 1000000000000000000)) * ((741597043 / 500000000000000000)) * (126 / 100) +
          2 * (((741597043 / 500000000000000000)) ^ 2 + 2 * ((4445799813 / 1000000000000000000)) * ((17824313 / 50000000000000000))) +
          6 * ((741597043 / 500000000000000000)) * ((17824313 / 50000000000000000)) * (126 / 100) + 8 * ((17824313 / 50000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12855) *
          (32 * (((4445799813 / 1000000000000000000) : ℝ) + (741597043 / 500000000000000000) + (17824313 / 50000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12855 : ℝ) ^ 16 *
      (d.w0 12855 164 + d.w1 12855 164 * √(π / 2) + 2 * d.w2 12855 164 +
        energyR16 12855 * radiusPolynomialRoot16 (d.w0 12855 164) (d.w1 12855 164)
          (d.w2 12855 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12855 : ℝ) ^ 16 *
        (((1767680409 / 100000000000000000000) : ℝ) + ((314417713 / 25000000000000000000)) * (126 / 100) + 2 * ((229760519 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12855) *
          (32 * (((1767680409 / 100000000000000000000) : ℝ) + (314417713 / 25000000000000000000) + (229760519 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12855

/-! A coarse bound on the actual paper statistics constant at dimension 12856. -/
namespace BstLean.Part266.Row12856
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12854 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12854 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12854 128 ≤ (13108 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13108 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12856) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12856 : ℕ))
    (by norm_num : (12856 : ℕ) ≤ 16384)
  have ht : paperTail256 12856 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12856 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12856 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12856 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12856 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12856 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12854 128 * √(2 / (12856 : ℝ)) *
      (√(12856 : ℝ) + paperT0 12856 + paperTail256 12856) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12856 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12856 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12856 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12854 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12854 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12856 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12856

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12856
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12856 (61 / 100) 164 (17 / (100 * 12856)) (26 / (10 * 12856)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12856 (61 / 100) 164 (17 / (100 * 12856)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (459409313 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1429400497 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (463903081 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12856 / 12856 * (61 / 100)) ^ 4 * inverseRadius8 (12856 - 1) /
            envelopeGap 12856 (61 / 100) 164 (17 / (100 * 12856)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12856

namespace BstLean.Part266.Row12856
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12856 164 ≤ (222246863 / 50000000000000000)
  f1 : (tableEnvelope C).f1 12856 164 ≤ (741453059 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (11138031 / 31250000000000000)
  w0 : (tableEnvelope C).w0 12856 164 ≤ (220908541 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12856 164 ≤ (125737757 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 12856 164 ≤ (459413807 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (459409313 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (459409313 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1429400497 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (463903081 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1818199 / 500000000) : ℝ) ≤ √(17 / (100 * 12856) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12856) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2143383571 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7561482651 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12856) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12856) ≤ (110004167 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12856) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12856 * (164 : ℝ) ^ 2 + 26 / (10 * 12856) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12856) : ℝ)) (tA 12856 * 164 ^ 2 + 26 / (10 * 12856)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1818199 / 500000000))) * ((459409313 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1818199 / 500000000)) ^ 3) * ((1429400497 / 1000000000000000000000000))) + ((463903081 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1818199 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12856) : ℝ)) d.D d.V d.P (√(tA 12856) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1818199 / 500000000)) ^ 2 * (((2143383571 / 1000000000000000)) * ((7561482651 / 200000000000000000)))) + ((463903081 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12856) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1818199 / 500000000)) * ((459409313 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12856) : ℝ)) (tA 12856 * 164 ^ 2 + 26 / (10 * 12856)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((459409313 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1818199 / 500000000)) ^ 2) * ((1429400497 / 1000000000000000000000000)) + ((463903081 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12856) : ℝ)) (√(26 / (10 * 12856) : ℝ)) d.D d.V d.P (√(tA 12856) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1818199 / 500000000)) * (((2143383571 / 1000000000000000)) * ((7561482651 / 200000000000000000))) + ((463903081 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12856) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((459409313 / 100000000000000000000) : ℝ) + ((463903081 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12856

namespace BstLean.Part266.Row12856
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12856 164 ∧
    0 ≤ (tableEnvelope C).f1 12856 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12856 164 ∧
    0 ≤ (tableEnvelope C).w1 12856 164 ∧ 0 ≤ (tableEnvelope C).w2 12856 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12856 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12856 164 ∧ 0 ≤ d.f1 12856 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12856 164 ∧ 0 ≤ d.w1 12856 164 ∧ 0 ≤ d.w2 12856 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12856 ≤ 2 * (228 / 100 : ℝ) / 12856 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12856 ≤ 2 * (370 / 100 : ℝ) / 12856 := by
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
    (completeRAData (tableEnvelope C) 12856 164).locationBound 12856 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12856 164).energyBound 12856 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12856 164) (d.f1 12856 164) d.f2 ≤
      32 * (((222246863 / 50000000000000000) : ℝ) + (741453059 / 500000000000000000) + (11138031 / 31250000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12856 164) (d.w1 12856 164)
      (d.w2 12856 164) ≤
      32 * (((220908541 / 12500000000000000000) : ℝ) + (125737757 / 10000000000000000000) + (459413807 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12856 164) (d.f1 12856 164) d.f2 ≤
      ((222246863 / 50000000000000000) : ℝ) ^ 2 + 2 * ((222246863 / 50000000000000000)) * ((741453059 / 500000000000000000)) * (126 / 100) +
      2 * (((741453059 / 500000000000000000)) ^ 2 + 2 * ((222246863 / 50000000000000000)) * ((11138031 / 31250000000000000))) +
      6 * ((741453059 / 500000000000000000)) * ((11138031 / 31250000000000000)) * (126 / 100) + 8 * ((11138031 / 31250000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12856 164) (d.f1 12856 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12856 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12856 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12856 164) (d.f1 12856 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12856 164) (d.w1 12856 164) (d.w2 12856 164)
  have hwexpr0 : 0 ≤ d.w0 12856 164 + d.w1 12856 164 * √(π / 2) +
      2 * d.w2 12856 164 + energyR16 12856 *
      radiusPolynomialRoot16 (d.w0 12856 164) (d.w1 12856 164) (d.w2 12856 164) := by
    positivity
  constructor
  · change (12856 : ℝ) ^ 8 * (mA 12856 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12856 164) (d.f1 12856 164) d.f2 + locationR16 12856 *
        radiusPolynomialRoot16 (d.f0 12856 164) (d.f1 12856 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12856 : ℝ) ^ 8 * (mA 12856 : ℝ) ^ 8 *
        ((((222246863 / 50000000000000000) : ℝ) ^ 2 + 2 * ((222246863 / 50000000000000000)) * ((741453059 / 500000000000000000)) * (126 / 100) +
          2 * (((741453059 / 500000000000000000)) ^ 2 + 2 * ((222246863 / 50000000000000000)) * ((11138031 / 31250000000000000))) +
          6 * ((741453059 / 500000000000000000)) * ((11138031 / 31250000000000000)) * (126 / 100) + 8 * ((11138031 / 31250000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12856) *
          (32 * (((222246863 / 50000000000000000) : ℝ) + (741453059 / 500000000000000000) + (11138031 / 31250000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12856 : ℝ) ^ 16 *
      (d.w0 12856 164 + d.w1 12856 164 * √(π / 2) + 2 * d.w2 12856 164 +
        energyR16 12856 * radiusPolynomialRoot16 (d.w0 12856 164) (d.w1 12856 164)
          (d.w2 12856 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12856 : ℝ) ^ 16 *
        (((220908541 / 12500000000000000000) : ℝ) + ((125737757 / 10000000000000000000)) * (126 / 100) + 2 * ((459413807 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12856) *
          (32 * (((220908541 / 12500000000000000000) : ℝ) + (125737757 / 10000000000000000000) + (459413807 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12856

/-! A coarse bound on the actual paper statistics constant at dimension 12857. -/
namespace BstLean.Part266.Row12857
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12855 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12855 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12855 128 ≤ (13109 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13109 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12857) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12857 : ℕ))
    (by norm_num : (12857 : ℕ) ≤ 16384)
  have ht : paperTail256 12857 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12857 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12857 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12857 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12857 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12857 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12855 128 * √(2 / (12857 : ℝ)) *
      (√(12857 : ℝ) + paperT0 12857 + paperTail256 12857) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12857 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12857 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12857 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12855 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12855 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12857 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12857

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12857
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12857 (61 / 100) 164 (17 / (100 * 12857)) (26 / (10 * 12857)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12857 (61 / 100) 164 (17 / (100 * 12857)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (459302119 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (89309739 / 62500000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4636117299 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12857 / 12857 * (61 / 100)) ^ 4 * inverseRadius8 (12857 - 1) /
            envelopeGap 12857 (61 / 100) 164 (17 / (100 * 12857)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12857

namespace BstLean.Part266.Row12857
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12857 164 ≤ (4444071471 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12857 164 ≤ (370654357 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (178173823 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12857 164 ≤ (1766855669 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12857 164 ≤ (31427101 / 2500000000000000000)
  w2 : (tableEnvelope C).w2 12857 164 ≤ (45930661 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (459302119 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (459302119 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (89309739 / 62500000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4636117299 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3636257 / 1000000000) : ℝ) ≤ √(17 / (100 * 12857) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12857) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1071566749 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37801532033 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12857) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12857) ≤ (109995611 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12857) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12857 * (164 : ℝ) ^ 2 + 26 / (10 * 12857) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12857) : ℝ)) (tA 12857 * 164 ^ 2 + 26 / (10 * 12857)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3636257 / 1000000000))) * ((459302119 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3636257 / 1000000000)) ^ 3) * ((89309739 / 62500000000000000000000))) + ((4636117299 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3636257 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12857) : ℝ)) d.D d.V d.P (√(tA 12857) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3636257 / 1000000000)) ^ 2 * (((1071566749 / 500000000000000)) * ((37801532033 / 1000000000000000000)))) + ((4636117299 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12857) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3636257 / 1000000000)) * ((459302119 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12857) : ℝ)) (tA 12857 * 164 ^ 2 + 26 / (10 * 12857)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((459302119 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3636257 / 1000000000)) ^ 2) * ((89309739 / 62500000000000000000000)) + ((4636117299 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12857) : ℝ)) (√(26 / (10 * 12857) : ℝ)) d.D d.V d.P (√(tA 12857) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3636257 / 1000000000)) * (((1071566749 / 500000000000000)) * ((37801532033 / 1000000000000000000))) + ((4636117299 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12857) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((459302119 / 100000000000000000000) : ℝ) + ((4636117299 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12857

namespace BstLean.Part266.Row12857
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12857 164 ∧
    0 ≤ (tableEnvelope C).f1 12857 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12857 164 ∧
    0 ≤ (tableEnvelope C).w1 12857 164 ∧ 0 ≤ (tableEnvelope C).w2 12857 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12857 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12857 164 ∧ 0 ≤ d.f1 12857 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12857 164 ∧ 0 ≤ d.w1 12857 164 ∧ 0 ≤ d.w2 12857 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12857 ≤ 2 * (228 / 100 : ℝ) / 12857 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12857 ≤ 2 * (370 / 100 : ℝ) / 12857 := by
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
    (completeRAData (tableEnvelope C) 12857 164).locationBound 12857 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12857 164).energyBound 12857 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12857 164) (d.f1 12857 164) d.f2 ≤
      32 * (((4444071471 / 1000000000000000000) : ℝ) + (370654357 / 250000000000000000) + (178173823 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12857 164) (d.w1 12857 164)
      (d.w2 12857 164) ≤
      32 * (((1766855669 / 100000000000000000000) : ℝ) + (31427101 / 2500000000000000000) + (45930661 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12857 164) (d.f1 12857 164) d.f2 ≤
      ((4444071471 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4444071471 / 1000000000000000000)) * ((370654357 / 250000000000000000)) * (126 / 100) +
      2 * (((370654357 / 250000000000000000)) ^ 2 + 2 * ((4444071471 / 1000000000000000000)) * ((178173823 / 500000000000000000))) +
      6 * ((370654357 / 250000000000000000)) * ((178173823 / 500000000000000000)) * (126 / 100) + 8 * ((178173823 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12857 164) (d.f1 12857 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12857 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12857 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12857 164) (d.f1 12857 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12857 164) (d.w1 12857 164) (d.w2 12857 164)
  have hwexpr0 : 0 ≤ d.w0 12857 164 + d.w1 12857 164 * √(π / 2) +
      2 * d.w2 12857 164 + energyR16 12857 *
      radiusPolynomialRoot16 (d.w0 12857 164) (d.w1 12857 164) (d.w2 12857 164) := by
    positivity
  constructor
  · change (12857 : ℝ) ^ 8 * (mA 12857 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12857 164) (d.f1 12857 164) d.f2 + locationR16 12857 *
        radiusPolynomialRoot16 (d.f0 12857 164) (d.f1 12857 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12857 : ℝ) ^ 8 * (mA 12857 : ℝ) ^ 8 *
        ((((4444071471 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4444071471 / 1000000000000000000)) * ((370654357 / 250000000000000000)) * (126 / 100) +
          2 * (((370654357 / 250000000000000000)) ^ 2 + 2 * ((4444071471 / 1000000000000000000)) * ((178173823 / 500000000000000000))) +
          6 * ((370654357 / 250000000000000000)) * ((178173823 / 500000000000000000)) * (126 / 100) + 8 * ((178173823 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12857) *
          (32 * (((4444071471 / 1000000000000000000) : ℝ) + (370654357 / 250000000000000000) + (178173823 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12857 : ℝ) ^ 16 *
      (d.w0 12857 164 + d.w1 12857 164 * √(π / 2) + 2 * d.w2 12857 164 +
        energyR16 12857 * radiusPolynomialRoot16 (d.w0 12857 164) (d.w1 12857 164)
          (d.w2 12857 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12857 : ℝ) ^ 16 *
        (((1766855669 / 100000000000000000000) : ℝ) + ((31427101 / 2500000000000000000)) * (126 / 100) + 2 * ((45930661 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12857) *
          (32 * (((1766855669 / 100000000000000000000) : ℝ) + (31427101 / 2500000000000000000) + (45930661 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12857

/-! A coarse bound on the actual paper statistics constant at dimension 12858. -/
namespace BstLean.Part266.Row12858
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12856 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12856 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12856 128 ≤ (13110 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13110 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12858) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12858 : ℕ))
    (by norm_num : (12858 : ℕ) ≤ 16384)
  have ht : paperTail256 12858 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12858 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12858 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12858 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12858 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12858 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12856 128 * √(2 / (12858 : ℝ)) *
      (√(12858 : ℝ) + paperT0 12858 + paperTail256 12858) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12858 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12858 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12858 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12856 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12856 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12858 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12858

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12858
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12858 (61 / 100) 164 (17 / (100 * 12858)) (26 / (10 * 12858)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12858 (61 / 100) 164 (17 / (100 * 12858)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (459194959 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (357127831 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (579150731 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12858 / 12858 * (61 / 100)) ^ 4 * inverseRadius8 (12858 - 1) /
            envelopeGap 12858 (61 / 100) 164 (17 / (100 * 12858)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12858

namespace BstLean.Part266.Row12858
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12858 164 ≤ (2221602989 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12858 164 ≤ (1482328831 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (178139161 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12858 164 ≤ (1766443151 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12858 164 ≤ (1256790609 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12858 164 ≤ (57399931 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (459194959 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (459194959 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (357127831 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (579150731 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((909029 / 250000000) : ℝ) ≤ √(17 / (100 * 12858) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12858) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (535720869 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4724456523 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12858) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12858) ≤ (6874191 / 62500000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12858) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12858 * (164 : ℝ) ^ 2 + 26 / (10 * 12858) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12858) : ℝ)) (tA 12858 * 164 ^ 2 + 26 / (10 * 12858)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((909029 / 250000000))) * ((459194959 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((909029 / 250000000)) ^ 3) * ((357127831 / 250000000000000000000000))) + ((579150731 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((909029 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12858) : ℝ)) d.D d.V d.P (√(tA 12858) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((909029 / 250000000)) ^ 2 * (((535720869 / 250000000000000)) * ((4724456523 / 125000000000000000)))) + ((579150731 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12858) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((909029 / 250000000)) * ((459194959 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12858) : ℝ)) (tA 12858 * 164 ^ 2 + 26 / (10 * 12858)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((459194959 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((909029 / 250000000)) ^ 2) * ((357127831 / 250000000000000000000000)) + ((579150731 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12858) : ℝ)) (√(26 / (10 * 12858) : ℝ)) d.D d.V d.P (√(tA 12858) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((909029 / 250000000)) * (((535720869 / 250000000000000)) * ((4724456523 / 125000000000000000))) + ((579150731 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12858) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((459194959 / 100000000000000000000) : ℝ) + ((579150731 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12858

namespace BstLean.Part266.Row12858
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12858 164 ∧
    0 ≤ (tableEnvelope C).f1 12858 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12858 164 ∧
    0 ≤ (tableEnvelope C).w1 12858 164 ∧ 0 ≤ (tableEnvelope C).w2 12858 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12858 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12858 164 ∧ 0 ≤ d.f1 12858 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12858 164 ∧ 0 ≤ d.w1 12858 164 ∧ 0 ≤ d.w2 12858 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12858 ≤ 2 * (228 / 100 : ℝ) / 12858 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12858 ≤ 2 * (370 / 100 : ℝ) / 12858 := by
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
    (completeRAData (tableEnvelope C) 12858 164).locationBound 12858 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12858 164).energyBound 12858 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12858 164) (d.f1 12858 164) d.f2 ≤
      32 * (((2221602989 / 500000000000000000) : ℝ) + (1482328831 / 1000000000000000000) + (178139161 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12858 164) (d.w1 12858 164)
      (d.w2 12858 164) ≤
      32 * (((1766443151 / 100000000000000000000) : ℝ) + (1256790609 / 100000000000000000000) + (57399931 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12858 164) (d.f1 12858 164) d.f2 ≤
      ((2221602989 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2221602989 / 500000000000000000)) * ((1482328831 / 1000000000000000000)) * (126 / 100) +
      2 * (((1482328831 / 1000000000000000000)) ^ 2 + 2 * ((2221602989 / 500000000000000000)) * ((178139161 / 500000000000000000))) +
      6 * ((1482328831 / 1000000000000000000)) * ((178139161 / 500000000000000000)) * (126 / 100) + 8 * ((178139161 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12858 164) (d.f1 12858 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12858 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12858 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12858 164) (d.f1 12858 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12858 164) (d.w1 12858 164) (d.w2 12858 164)
  have hwexpr0 : 0 ≤ d.w0 12858 164 + d.w1 12858 164 * √(π / 2) +
      2 * d.w2 12858 164 + energyR16 12858 *
      radiusPolynomialRoot16 (d.w0 12858 164) (d.w1 12858 164) (d.w2 12858 164) := by
    positivity
  constructor
  · change (12858 : ℝ) ^ 8 * (mA 12858 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12858 164) (d.f1 12858 164) d.f2 + locationR16 12858 *
        radiusPolynomialRoot16 (d.f0 12858 164) (d.f1 12858 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12858 : ℝ) ^ 8 * (mA 12858 : ℝ) ^ 8 *
        ((((2221602989 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2221602989 / 500000000000000000)) * ((1482328831 / 1000000000000000000)) * (126 / 100) +
          2 * (((1482328831 / 1000000000000000000)) ^ 2 + 2 * ((2221602989 / 500000000000000000)) * ((178139161 / 500000000000000000))) +
          6 * ((1482328831 / 1000000000000000000)) * ((178139161 / 500000000000000000)) * (126 / 100) + 8 * ((178139161 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12858) *
          (32 * (((2221602989 / 500000000000000000) : ℝ) + (1482328831 / 1000000000000000000) + (178139161 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12858 : ℝ) ^ 16 *
      (d.w0 12858 164 + d.w1 12858 164 * √(π / 2) + 2 * d.w2 12858 164 +
        energyR16 12858 * radiusPolynomialRoot16 (d.w0 12858 164) (d.w1 12858 164)
          (d.w2 12858 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12858 : ℝ) ^ 16 *
        (((1766443151 / 100000000000000000000) : ℝ) + ((1256790609 / 100000000000000000000)) * (126 / 100) + 2 * ((57399931 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12858) *
          (32 * (((1766443151 / 100000000000000000000) : ℝ) + (1256790609 / 100000000000000000000) + (57399931 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12858

/-! A coarse bound on the actual paper statistics constant at dimension 12859. -/
namespace BstLean.Part266.Row12859
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12857 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12857 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12857 128 ≤ (13111 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13111 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12859) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12859 : ℕ))
    (by norm_num : (12859 : ℕ) ≤ 16384)
  have ht : paperTail256 12859 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12859 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12859 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12859 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12859 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12859 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12857 128 * √(2 / (12859 : ℝ)) *
      (√(12859 : ℝ) + paperT0 12859 + paperTail256 12859) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12859 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12859 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12859 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12857 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12857 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12859 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12859

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12859
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12859 (61 / 100) 164 (17 / (100 * 12859)) (26 / (10 * 12859)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12859 (61 / 100) 164 (17 / (100 * 12859)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (57385979 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1428066997 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (578787057 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12859 / 12859 * (61 / 100)) ^ 4 * inverseRadius8 (12859 - 1) /
            envelopeGap 12859 (61 / 100) 164 (17 / (100 * 12859)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12859

namespace BstLean.Part266.Row12859
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12859 164 ≤ (888468861 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12859 164 ≤ (1482041141 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (71241823 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12859 164 ≤ (1766031491 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12859 164 ≤ (62824881 / 5000000000000000000)
  w2 : (tableEnvelope C).w2 12859 164 ≤ (229546159 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (57385979 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (57385979 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1428066997 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (578787057 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1817987 / 500000000) : ℝ) ≤ √(17 / (100 * 12859) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12859) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1071316751 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3778977371 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12859) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12859) ≤ (109978503 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12859) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12859 * (164 : ℝ) ^ 2 + 26 / (10 * 12859) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12859) : ℝ)) (tA 12859 * 164 ^ 2 + 26 / (10 * 12859)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1817987 / 500000000))) * ((57385979 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1817987 / 500000000)) ^ 3) * ((1428066997 / 1000000000000000000000000))) + ((578787057 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1817987 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12859) : ℝ)) d.D d.V d.P (√(tA 12859) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1817987 / 500000000)) ^ 2 * (((1071316751 / 500000000000000)) * ((3778977371 / 100000000000000000)))) + ((578787057 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12859) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1817987 / 500000000)) * ((57385979 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12859) : ℝ)) (tA 12859 * 164 ^ 2 + 26 / (10 * 12859)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((57385979 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1817987 / 500000000)) ^ 2) * ((1428066997 / 1000000000000000000000000)) + ((578787057 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12859) : ℝ)) (√(26 / (10 * 12859) : ℝ)) d.D d.V d.P (√(tA 12859) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1817987 / 500000000)) * (((1071316751 / 500000000000000)) * ((3778977371 / 100000000000000000))) + ((578787057 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12859) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((57385979 / 12500000000000000000) : ℝ) + ((578787057 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12859

namespace BstLean.Part266.Row12859
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12859 164 ∧
    0 ≤ (tableEnvelope C).f1 12859 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12859 164 ∧
    0 ≤ (tableEnvelope C).w1 12859 164 ∧ 0 ≤ (tableEnvelope C).w2 12859 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12859 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12859 164 ∧ 0 ≤ d.f1 12859 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12859 164 ∧ 0 ≤ d.w1 12859 164 ∧ 0 ≤ d.w2 12859 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12859 ≤ 2 * (228 / 100 : ℝ) / 12859 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12859 ≤ 2 * (370 / 100 : ℝ) / 12859 := by
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
    (completeRAData (tableEnvelope C) 12859 164).locationBound 12859 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12859 164).energyBound 12859 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12859 164) (d.f1 12859 164) d.f2 ≤
      32 * (((888468861 / 200000000000000000) : ℝ) + (1482041141 / 1000000000000000000) + (71241823 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12859 164) (d.w1 12859 164)
      (d.w2 12859 164) ≤
      32 * (((1766031491 / 100000000000000000000) : ℝ) + (62824881 / 5000000000000000000) + (229546159 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12859 164) (d.f1 12859 164) d.f2 ≤
      ((888468861 / 200000000000000000) : ℝ) ^ 2 + 2 * ((888468861 / 200000000000000000)) * ((1482041141 / 1000000000000000000)) * (126 / 100) +
      2 * (((1482041141 / 1000000000000000000)) ^ 2 + 2 * ((888468861 / 200000000000000000)) * ((71241823 / 200000000000000000))) +
      6 * ((1482041141 / 1000000000000000000)) * ((71241823 / 200000000000000000)) * (126 / 100) + 8 * ((71241823 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12859 164) (d.f1 12859 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12859 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12859 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12859 164) (d.f1 12859 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12859 164) (d.w1 12859 164) (d.w2 12859 164)
  have hwexpr0 : 0 ≤ d.w0 12859 164 + d.w1 12859 164 * √(π / 2) +
      2 * d.w2 12859 164 + energyR16 12859 *
      radiusPolynomialRoot16 (d.w0 12859 164) (d.w1 12859 164) (d.w2 12859 164) := by
    positivity
  constructor
  · change (12859 : ℝ) ^ 8 * (mA 12859 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12859 164) (d.f1 12859 164) d.f2 + locationR16 12859 *
        radiusPolynomialRoot16 (d.f0 12859 164) (d.f1 12859 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12859 : ℝ) ^ 8 * (mA 12859 : ℝ) ^ 8 *
        ((((888468861 / 200000000000000000) : ℝ) ^ 2 + 2 * ((888468861 / 200000000000000000)) * ((1482041141 / 1000000000000000000)) * (126 / 100) +
          2 * (((1482041141 / 1000000000000000000)) ^ 2 + 2 * ((888468861 / 200000000000000000)) * ((71241823 / 200000000000000000))) +
          6 * ((1482041141 / 1000000000000000000)) * ((71241823 / 200000000000000000)) * (126 / 100) + 8 * ((71241823 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12859) *
          (32 * (((888468861 / 200000000000000000) : ℝ) + (1482041141 / 1000000000000000000) + (71241823 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12859 : ℝ) ^ 16 *
      (d.w0 12859 164 + d.w1 12859 164 * √(π / 2) + 2 * d.w2 12859 164 +
        energyR16 12859 * radiusPolynomialRoot16 (d.w0 12859 164) (d.w1 12859 164)
          (d.w2 12859 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12859 : ℝ) ^ 16 *
        (((1766031491 / 100000000000000000000) : ℝ) + ((62824881 / 5000000000000000000)) * (126 / 100) + 2 * ((229546159 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12859) *
          (32 * (((1766031491 / 100000000000000000000) : ℝ) + (62824881 / 5000000000000000000) + (229546159 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12859

/-! A coarse bound on the actual paper statistics constant at dimension 12860. -/
namespace BstLean.Part266.Row12860
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12858 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12858 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12858 128 ≤ (13112 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13112 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12860) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12860 : ℕ))
    (by norm_num : (12860 : ℕ) ≤ 16384)
  have ht : paperTail256 12860 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12860 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12860 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12860 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12860 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12860 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12858 128 * √(2 / (12860 : ℝ)) *
      (√(12860 : ℝ) + paperT0 12860 + paperTail256 12860) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12860 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12860 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12860 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12858 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12858 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12860 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12860

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12860
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12860 (61 / 100) 164 (17 / (100 * 12860)) (26 / (10 * 12860)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12860 (61 / 100) 164 (17 / (100 * 12860)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (229490369 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1427622843 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4627389121 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12860 / 12860 * (61 / 100)) ^ 4 * inverseRadius8 (12860 - 1) /
            envelopeGap 12860 (61 / 100) 164 (17 / (100 * 12860)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12860

namespace BstLean.Part266.Row12860
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12860 164 ≤ (4441479399 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12860 164 ≤ (1481752727 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (356139831 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12860 164 ≤ (1765619253 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12860 164 ≤ (628102191 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12860 164 ≤ (458985221 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (229490369 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (229490369 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1427622843 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4627389121 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3635833 / 1000000000) : ℝ) ≤ √(17 / (100 * 12860) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12860) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (85695343 / 40000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3778389661 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12860) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12860) ≤ (109969951 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12860) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12860 * (164 : ℝ) ^ 2 + 26 / (10 * 12860) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12860) : ℝ)) (tA 12860 * 164 ^ 2 + 26 / (10 * 12860)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3635833 / 1000000000))) * ((229490369 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3635833 / 1000000000)) ^ 3) * ((1427622843 / 1000000000000000000000000))) + ((4627389121 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3635833 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12860) : ℝ)) d.D d.V d.P (√(tA 12860) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3635833 / 1000000000)) ^ 2 * (((85695343 / 40000000000000)) * ((3778389661 / 100000000000000000)))) + ((4627389121 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12860) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3635833 / 1000000000)) * ((229490369 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12860) : ℝ)) (tA 12860 * 164 ^ 2 + 26 / (10 * 12860)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((229490369 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3635833 / 1000000000)) ^ 2) * ((1427622843 / 1000000000000000000000000)) + ((4627389121 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12860) : ℝ)) (√(26 / (10 * 12860) : ℝ)) d.D d.V d.P (√(tA 12860) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3635833 / 1000000000)) * (((85695343 / 40000000000000)) * ((3778389661 / 100000000000000000))) + ((4627389121 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12860) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((229490369 / 50000000000000000000) : ℝ) + ((4627389121 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12860

namespace BstLean.Part266.Row12860
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12860 164 ∧
    0 ≤ (tableEnvelope C).f1 12860 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12860 164 ∧
    0 ≤ (tableEnvelope C).w1 12860 164 ∧ 0 ≤ (tableEnvelope C).w2 12860 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12860 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12860 164 ∧ 0 ≤ d.f1 12860 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12860 164 ∧ 0 ≤ d.w1 12860 164 ∧ 0 ≤ d.w2 12860 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12860 ≤ 2 * (228 / 100 : ℝ) / 12860 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12860 ≤ 2 * (370 / 100 : ℝ) / 12860 := by
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
    (completeRAData (tableEnvelope C) 12860 164).locationBound 12860 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12860 164).energyBound 12860 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12860 164) (d.f1 12860 164) d.f2 ≤
      32 * (((4441479399 / 1000000000000000000) : ℝ) + (1481752727 / 1000000000000000000) + (356139831 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12860 164) (d.w1 12860 164)
      (d.w2 12860 164) ≤
      32 * (((1765619253 / 100000000000000000000) : ℝ) + (628102191 / 50000000000000000000) + (458985221 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12860 164) (d.f1 12860 164) d.f2 ≤
      ((4441479399 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4441479399 / 1000000000000000000)) * ((1481752727 / 1000000000000000000)) * (126 / 100) +
      2 * (((1481752727 / 1000000000000000000)) ^ 2 + 2 * ((4441479399 / 1000000000000000000)) * ((356139831 / 1000000000000000000))) +
      6 * ((1481752727 / 1000000000000000000)) * ((356139831 / 1000000000000000000)) * (126 / 100) + 8 * ((356139831 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12860 164) (d.f1 12860 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12860 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12860 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12860 164) (d.f1 12860 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12860 164) (d.w1 12860 164) (d.w2 12860 164)
  have hwexpr0 : 0 ≤ d.w0 12860 164 + d.w1 12860 164 * √(π / 2) +
      2 * d.w2 12860 164 + energyR16 12860 *
      radiusPolynomialRoot16 (d.w0 12860 164) (d.w1 12860 164) (d.w2 12860 164) := by
    positivity
  constructor
  · change (12860 : ℝ) ^ 8 * (mA 12860 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12860 164) (d.f1 12860 164) d.f2 + locationR16 12860 *
        radiusPolynomialRoot16 (d.f0 12860 164) (d.f1 12860 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12860 : ℝ) ^ 8 * (mA 12860 : ℝ) ^ 8 *
        ((((4441479399 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4441479399 / 1000000000000000000)) * ((1481752727 / 1000000000000000000)) * (126 / 100) +
          2 * (((1481752727 / 1000000000000000000)) ^ 2 + 2 * ((4441479399 / 1000000000000000000)) * ((356139831 / 1000000000000000000))) +
          6 * ((1481752727 / 1000000000000000000)) * ((356139831 / 1000000000000000000)) * (126 / 100) + 8 * ((356139831 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12860) *
          (32 * (((4441479399 / 1000000000000000000) : ℝ) + (1481752727 / 1000000000000000000) + (356139831 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12860 : ℝ) ^ 16 *
      (d.w0 12860 164 + d.w1 12860 164 * √(π / 2) + 2 * d.w2 12860 164 +
        energyR16 12860 * radiusPolynomialRoot16 (d.w0 12860 164) (d.w1 12860 164)
          (d.w2 12860 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12860 : ℝ) ^ 16 *
        (((1765619253 / 100000000000000000000) : ℝ) + ((628102191 / 50000000000000000000)) * (126 / 100) + 2 * ((458985221 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12860) *
          (32 * (((1765619253 / 100000000000000000000) : ℝ) + (628102191 / 50000000000000000000) + (458985221 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12860

/-! A coarse bound on the actual paper statistics constant at dimension 12861. -/
namespace BstLean.Part266.Row12861
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12859 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12859 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12859 128 ≤ (13113 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13113 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12861) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12861 : ℕ))
    (by norm_num : (12861 : ℕ) ≤ 16384)
  have ht : paperTail256 12861 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12861 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12861 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12861 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12861 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12861 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12859 128 * √(2 / (12861 : ℝ)) *
      (√(12861 : ℝ) + paperT0 12861 + paperTail256 12861) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12861 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12861 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12861 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12859 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12859 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12861 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12861

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12861
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12861 (61 / 100) 164 (17 / (100 * 12861)) (26 / (10 * 12861)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12861 (61 / 100) 164 (17 / (100 * 12861)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (458873677 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1427178861 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2312241921 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12861 / 12861 * (61 / 100)) ^ 4 * inverseRadius8 (12861 - 1) /
            envelopeGap 12861 (61 / 100) 164 (17 / (100 * 12861)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12861

namespace BstLean.Part266.Row12861
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12861 164 ≤ (34692303 / 7812500000000000)
  f1 : (tableEnvelope C).f1 12861 164 ≤ (370366101 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (356070567 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12861 164 ≤ (882603577 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12861 164 ≤ (1255911239 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12861 164 ≤ (458878157 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (458873677 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (458873677 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1427178861 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2312241921 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((908923 / 250000000) : ℝ) ≤ √(17 / (100 * 12861) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12861) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (33470839 / 15625000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4722252609 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12861) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12861) ≤ (549807 / 5000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12861) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12861 * (164 : ℝ) ^ 2 + 26 / (10 * 12861) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12861) : ℝ)) (tA 12861 * 164 ^ 2 + 26 / (10 * 12861)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((908923 / 250000000))) * ((458873677 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((908923 / 250000000)) ^ 3) * ((1427178861 / 1000000000000000000000000))) + ((2312241921 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((908923 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12861) : ℝ)) d.D d.V d.P (√(tA 12861) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((908923 / 250000000)) ^ 2 * (((33470839 / 15625000000000)) * ((4722252609 / 125000000000000000)))) + ((2312241921 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12861) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((908923 / 250000000)) * ((458873677 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12861) : ℝ)) (tA 12861 * 164 ^ 2 + 26 / (10 * 12861)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((458873677 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((908923 / 250000000)) ^ 2) * ((1427178861 / 1000000000000000000000000)) + ((2312241921 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12861) : ℝ)) (√(26 / (10 * 12861) : ℝ)) d.D d.V d.P (√(tA 12861) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((908923 / 250000000)) * (((33470839 / 15625000000000)) * ((4722252609 / 125000000000000000))) + ((2312241921 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12861) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((458873677 / 100000000000000000000) : ℝ) + ((2312241921 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12861

namespace BstLean.Part266.Row12861
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12861 164 ∧
    0 ≤ (tableEnvelope C).f1 12861 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12861 164 ∧
    0 ≤ (tableEnvelope C).w1 12861 164 ∧ 0 ≤ (tableEnvelope C).w2 12861 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12861 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12861 164 ∧ 0 ≤ d.f1 12861 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12861 164 ∧ 0 ≤ d.w1 12861 164 ∧ 0 ≤ d.w2 12861 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12861 ≤ 2 * (228 / 100 : ℝ) / 12861 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12861 ≤ 2 * (370 / 100 : ℝ) / 12861 := by
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
    (completeRAData (tableEnvelope C) 12861 164).locationBound 12861 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12861 164).energyBound 12861 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12861 164) (d.f1 12861 164) d.f2 ≤
      32 * (((34692303 / 7812500000000000) : ℝ) + (370366101 / 250000000000000000) + (356070567 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12861 164) (d.w1 12861 164)
      (d.w2 12861 164) ≤
      32 * (((882603577 / 50000000000000000000) : ℝ) + (1255911239 / 100000000000000000000) + (458878157 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12861 164) (d.f1 12861 164) d.f2 ≤
      ((34692303 / 7812500000000000) : ℝ) ^ 2 + 2 * ((34692303 / 7812500000000000)) * ((370366101 / 250000000000000000)) * (126 / 100) +
      2 * (((370366101 / 250000000000000000)) ^ 2 + 2 * ((34692303 / 7812500000000000)) * ((356070567 / 1000000000000000000))) +
      6 * ((370366101 / 250000000000000000)) * ((356070567 / 1000000000000000000)) * (126 / 100) + 8 * ((356070567 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12861 164) (d.f1 12861 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12861 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12861 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12861 164) (d.f1 12861 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12861 164) (d.w1 12861 164) (d.w2 12861 164)
  have hwexpr0 : 0 ≤ d.w0 12861 164 + d.w1 12861 164 * √(π / 2) +
      2 * d.w2 12861 164 + energyR16 12861 *
      radiusPolynomialRoot16 (d.w0 12861 164) (d.w1 12861 164) (d.w2 12861 164) := by
    positivity
  constructor
  · change (12861 : ℝ) ^ 8 * (mA 12861 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12861 164) (d.f1 12861 164) d.f2 + locationR16 12861 *
        radiusPolynomialRoot16 (d.f0 12861 164) (d.f1 12861 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12861 : ℝ) ^ 8 * (mA 12861 : ℝ) ^ 8 *
        ((((34692303 / 7812500000000000) : ℝ) ^ 2 + 2 * ((34692303 / 7812500000000000)) * ((370366101 / 250000000000000000)) * (126 / 100) +
          2 * (((370366101 / 250000000000000000)) ^ 2 + 2 * ((34692303 / 7812500000000000)) * ((356070567 / 1000000000000000000))) +
          6 * ((370366101 / 250000000000000000)) * ((356070567 / 1000000000000000000)) * (126 / 100) + 8 * ((356070567 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12861) *
          (32 * (((34692303 / 7812500000000000) : ℝ) + (370366101 / 250000000000000000) + (356070567 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12861 : ℝ) ^ 16 *
      (d.w0 12861 164 + d.w1 12861 164 * √(π / 2) + 2 * d.w2 12861 164 +
        energyR16 12861 * radiusPolynomialRoot16 (d.w0 12861 164) (d.w1 12861 164)
          (d.w2 12861 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12861 : ℝ) ^ 16 *
        (((882603577 / 50000000000000000000) : ℝ) + ((1255911239 / 100000000000000000000)) * (126 / 100) + 2 * ((458878157 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12861) *
          (32 * (((882603577 / 50000000000000000000) : ℝ) + (1255911239 / 100000000000000000000) + (458878157 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12861

/-! A coarse bound on the actual paper statistics constant at dimension 12862. -/
namespace BstLean.Part266.Row12862
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12860 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12860 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12860 128 ≤ (13114 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13114 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12862) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12862 : ℕ))
    (by norm_num : (12862 : ℕ) ≤ 16384)
  have ht : paperTail256 12862 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12862 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12862 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12862 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12862 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12862 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12860 128 * √(2 / (12862 : ℝ)) *
      (√(12862 : ℝ) + paperT0 12862 + paperTail256 12862) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12862 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12862 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12862 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12860 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12860 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12862 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12862

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12862
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12862 (61 / 100) 164 (17 / (100 * 12862)) (26 / (10 * 12862)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12862 (61 / 100) 164 (17 / (100 * 12862)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (9175333 / 2000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (356683763 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4621580617 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12862 / 12862 * (61 / 100)) ^ 4 * inverseRadius8 (12862 - 1) /
            envelopeGap 12862 (61 / 100) 164 (17 / (100 * 12862)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12862

namespace BstLean.Part266.Row12862
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12862 164 ≤ (443975399 / 100000000000000000)
  f1 : (tableEnvelope C).f1 12862 164 ≤ (148117699 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (178000711 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12862 164 ≤ (352959183 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12862 164 ≤ (1255618541 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12862 164 ≤ (458771127 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (9175333 / 2000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (9175333 / 2000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (356683763 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4621580617 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((72711 / 20000000) : ℝ) ≤ √(17 / (100 * 12862) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12862) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (535470967 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37772146511 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12862) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12862) ≤ (109952851 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12862) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12862 * (164 : ℝ) ^ 2 + 26 / (10 * 12862) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12862) : ℝ)) (tA 12862 * 164 ^ 2 + 26 / (10 * 12862)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((72711 / 20000000))) * ((9175333 / 2000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((72711 / 20000000)) ^ 3) * ((356683763 / 250000000000000000000000))) + ((4621580617 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((72711 / 20000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12862) : ℝ)) d.D d.V d.P (√(tA 12862) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((72711 / 20000000)) ^ 2 * (((535470967 / 250000000000000)) * ((37772146511 / 1000000000000000000)))) + ((4621580617 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12862) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((72711 / 20000000)) * ((9175333 / 2000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12862) : ℝ)) (tA 12862 * 164 ^ 2 + 26 / (10 * 12862)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((9175333 / 2000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((72711 / 20000000)) ^ 2) * ((356683763 / 250000000000000000000000)) + ((4621580617 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12862) : ℝ)) (√(26 / (10 * 12862) : ℝ)) d.D d.V d.P (√(tA 12862) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((72711 / 20000000)) * (((535470967 / 250000000000000)) * ((37772146511 / 1000000000000000000))) + ((4621580617 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12862) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((9175333 / 2000000000000000000) : ℝ) + ((4621580617 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12862

namespace BstLean.Part266.Row12862
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12862 164 ∧
    0 ≤ (tableEnvelope C).f1 12862 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12862 164 ∧
    0 ≤ (tableEnvelope C).w1 12862 164 ∧ 0 ≤ (tableEnvelope C).w2 12862 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12862 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12862 164 ∧ 0 ≤ d.f1 12862 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12862 164 ∧ 0 ≤ d.w1 12862 164 ∧ 0 ≤ d.w2 12862 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12862 ≤ 2 * (228 / 100 : ℝ) / 12862 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12862 ≤ 2 * (370 / 100 : ℝ) / 12862 := by
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
    (completeRAData (tableEnvelope C) 12862 164).locationBound 12862 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12862 164).energyBound 12862 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12862 164) (d.f1 12862 164) d.f2 ≤
      32 * (((443975399 / 100000000000000000) : ℝ) + (148117699 / 100000000000000000) + (178000711 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12862 164) (d.w1 12862 164)
      (d.w2 12862 164) ≤
      32 * (((352959183 / 20000000000000000000) : ℝ) + (1255618541 / 100000000000000000000) + (458771127 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12862 164) (d.f1 12862 164) d.f2 ≤
      ((443975399 / 100000000000000000) : ℝ) ^ 2 + 2 * ((443975399 / 100000000000000000)) * ((148117699 / 100000000000000000)) * (126 / 100) +
      2 * (((148117699 / 100000000000000000)) ^ 2 + 2 * ((443975399 / 100000000000000000)) * ((178000711 / 500000000000000000))) +
      6 * ((148117699 / 100000000000000000)) * ((178000711 / 500000000000000000)) * (126 / 100) + 8 * ((178000711 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12862 164) (d.f1 12862 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12862 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12862 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12862 164) (d.f1 12862 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12862 164) (d.w1 12862 164) (d.w2 12862 164)
  have hwexpr0 : 0 ≤ d.w0 12862 164 + d.w1 12862 164 * √(π / 2) +
      2 * d.w2 12862 164 + energyR16 12862 *
      radiusPolynomialRoot16 (d.w0 12862 164) (d.w1 12862 164) (d.w2 12862 164) := by
    positivity
  constructor
  · change (12862 : ℝ) ^ 8 * (mA 12862 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12862 164) (d.f1 12862 164) d.f2 + locationR16 12862 *
        radiusPolynomialRoot16 (d.f0 12862 164) (d.f1 12862 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12862 : ℝ) ^ 8 * (mA 12862 : ℝ) ^ 8 *
        ((((443975399 / 100000000000000000) : ℝ) ^ 2 + 2 * ((443975399 / 100000000000000000)) * ((148117699 / 100000000000000000)) * (126 / 100) +
          2 * (((148117699 / 100000000000000000)) ^ 2 + 2 * ((443975399 / 100000000000000000)) * ((178000711 / 500000000000000000))) +
          6 * ((148117699 / 100000000000000000)) * ((178000711 / 500000000000000000)) * (126 / 100) + 8 * ((178000711 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12862) *
          (32 * (((443975399 / 100000000000000000) : ℝ) + (148117699 / 100000000000000000) + (178000711 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12862 : ℝ) ^ 16 *
      (d.w0 12862 164 + d.w1 12862 164 * √(π / 2) + 2 * d.w2 12862 164 +
        energyR16 12862 * radiusPolynomialRoot16 (d.w0 12862 164) (d.w1 12862 164)
          (d.w2 12862 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12862 : ℝ) ^ 16 *
        (((352959183 / 20000000000000000000) : ℝ) + ((1255618541 / 100000000000000000000)) * (126 / 100) + 2 * ((458771127 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12862) *
          (32 * (((352959183 / 20000000000000000000) : ℝ) + (1255618541 / 100000000000000000000) + (458771127 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12862

/-! A coarse bound on the actual paper statistics constant at dimension 12863. -/
namespace BstLean.Part266.Row12863
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12861 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12861 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12861 128 ≤ (13115 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13115 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12863) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12863 : ℕ))
    (by norm_num : (12863 : ℕ) ≤ 16384)
  have ht : paperTail256 12863 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12863 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12863 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12863 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12863 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12863 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12861 128 * √(2 / (12863 : ℝ)) *
      (√(12863 : ℝ) + paperT0 12863 + paperTail256 12863) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12863 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12863 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12863 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12861 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12861 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12863 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12863

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12863
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12863 (61 / 100) 164 (17 / (100 * 12863)) (26 / (10 * 12863)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12863 (61 / 100) 164 (17 / (100 * 12863)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (57332457 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (178286427 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (923735889 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12863 / 12863 * (61 / 100)) ^ 4 * inverseRadius8 (12863 - 1) /
            envelopeGap 12863 (61 / 100) 164 (17 / (100 * 12863)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12863

namespace BstLean.Part266.Row12863
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12863 164 ≤ (887777993 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12863 164 ≤ (370222213 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (1779661 / 5000000000000000)
  w0 : (tableEnvelope C).w0 12863 164 ≤ (1764384097 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12863 164 ≤ (1255325593 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12863 164 ≤ (458664131 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (57332457 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (57332457 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (178286427 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (923735889 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3635409 / 1000000000) : ℝ) ≤ √(17 / (100 * 12863) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12863) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2141634087 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18883136763 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12863) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12863) ≤ (109944303 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12863) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12863 * (164 : ℝ) ^ 2 + 26 / (10 * 12863) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12863) : ℝ)) (tA 12863 * 164 ^ 2 + 26 / (10 * 12863)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3635409 / 1000000000))) * ((57332457 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3635409 / 1000000000)) ^ 3) * ((178286427 / 125000000000000000000000))) + ((923735889 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3635409 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12863) : ℝ)) d.D d.V d.P (√(tA 12863) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3635409 / 1000000000)) ^ 2 * (((2141634087 / 1000000000000000)) * ((18883136763 / 500000000000000000)))) + ((923735889 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12863) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3635409 / 1000000000)) * ((57332457 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12863) : ℝ)) (tA 12863 * 164 ^ 2 + 26 / (10 * 12863)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((57332457 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3635409 / 1000000000)) ^ 2) * ((178286427 / 125000000000000000000000)) + ((923735889 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12863) : ℝ)) (√(26 / (10 * 12863) : ℝ)) d.D d.V d.P (√(tA 12863) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3635409 / 1000000000)) * (((2141634087 / 1000000000000000)) * ((18883136763 / 500000000000000000))) + ((923735889 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12863) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((57332457 / 12500000000000000000) : ℝ) + ((923735889 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12863

namespace BstLean.Part266.Row12863
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12863 164 ∧
    0 ≤ (tableEnvelope C).f1 12863 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12863 164 ∧
    0 ≤ (tableEnvelope C).w1 12863 164 ∧ 0 ≤ (tableEnvelope C).w2 12863 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12863 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12863 164 ∧ 0 ≤ d.f1 12863 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12863 164 ∧ 0 ≤ d.w1 12863 164 ∧ 0 ≤ d.w2 12863 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12863 ≤ 2 * (228 / 100 : ℝ) / 12863 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12863 ≤ 2 * (370 / 100 : ℝ) / 12863 := by
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
    (completeRAData (tableEnvelope C) 12863 164).locationBound 12863 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12863 164).energyBound 12863 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12863 164) (d.f1 12863 164) d.f2 ≤
      32 * (((887777993 / 200000000000000000) : ℝ) + (370222213 / 250000000000000000) + (1779661 / 5000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12863 164) (d.w1 12863 164)
      (d.w2 12863 164) ≤
      32 * (((1764384097 / 100000000000000000000) : ℝ) + (1255325593 / 100000000000000000000) + (458664131 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12863 164) (d.f1 12863 164) d.f2 ≤
      ((887777993 / 200000000000000000) : ℝ) ^ 2 + 2 * ((887777993 / 200000000000000000)) * ((370222213 / 250000000000000000)) * (126 / 100) +
      2 * (((370222213 / 250000000000000000)) ^ 2 + 2 * ((887777993 / 200000000000000000)) * ((1779661 / 5000000000000000))) +
      6 * ((370222213 / 250000000000000000)) * ((1779661 / 5000000000000000)) * (126 / 100) + 8 * ((1779661 / 5000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12863 164) (d.f1 12863 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12863 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12863 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12863 164) (d.f1 12863 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12863 164) (d.w1 12863 164) (d.w2 12863 164)
  have hwexpr0 : 0 ≤ d.w0 12863 164 + d.w1 12863 164 * √(π / 2) +
      2 * d.w2 12863 164 + energyR16 12863 *
      radiusPolynomialRoot16 (d.w0 12863 164) (d.w1 12863 164) (d.w2 12863 164) := by
    positivity
  constructor
  · change (12863 : ℝ) ^ 8 * (mA 12863 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12863 164) (d.f1 12863 164) d.f2 + locationR16 12863 *
        radiusPolynomialRoot16 (d.f0 12863 164) (d.f1 12863 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12863 : ℝ) ^ 8 * (mA 12863 : ℝ) ^ 8 *
        ((((887777993 / 200000000000000000) : ℝ) ^ 2 + 2 * ((887777993 / 200000000000000000)) * ((370222213 / 250000000000000000)) * (126 / 100) +
          2 * (((370222213 / 250000000000000000)) ^ 2 + 2 * ((887777993 / 200000000000000000)) * ((1779661 / 5000000000000000))) +
          6 * ((370222213 / 250000000000000000)) * ((1779661 / 5000000000000000)) * (126 / 100) + 8 * ((1779661 / 5000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12863) *
          (32 * (((887777993 / 200000000000000000) : ℝ) + (370222213 / 250000000000000000) + (1779661 / 5000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12863 : ℝ) ^ 16 *
      (d.w0 12863 164 + d.w1 12863 164 * √(π / 2) + 2 * d.w2 12863 164 +
        energyR16 12863 * radiusPolynomialRoot16 (d.w0 12863 164) (d.w1 12863 164)
          (d.w2 12863 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12863 : ℝ) ^ 16 *
        (((1764384097 / 100000000000000000000) : ℝ) + ((1255325593 / 100000000000000000000)) * (126 / 100) + 2 * ((458664131 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12863) *
          (32 * (((1764384097 / 100000000000000000000) : ℝ) + (1255325593 / 100000000000000000000) + (458664131 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12863

/-! A coarse bound on the actual paper statistics constant at dimension 12864. -/
namespace BstLean.Part266.Row12864
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12862 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12862 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12862 128 ≤ (13116 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13116 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12864) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12864 : ℕ))
    (by norm_num : (12864 : ℕ) ≤ 16384)
  have ht : paperTail256 12864 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12864 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12864 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12864 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12864 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12864 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12862 128 * √(2 / (12864 : ℝ)) *
      (√(12864 : ℝ) + paperT0 12864 + paperTail256 12864) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12864 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12864 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12864 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12862 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12862 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12864 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12864

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12864
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12864 (61 / 100) 164 (17 / (100 * 12864)) (26 / (10 * 12864)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12864 (61 / 100) 164 (17 / (100 * 12864)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (91710539 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (89115497 / 62500000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4615780323 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12864 / 12864 * (61 / 100)) ^ 4 * inverseRadius8 (12864 - 1) /
            envelopeGap 12864 (61 / 100) 164 (17 / (100 * 12864)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12864

namespace BstLean.Part266.Row12864
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12864 164 ≤ (4438026231 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12864 164 ≤ (296120161 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (355862997 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12864 164 ≤ (881986209 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12864 164 ≤ (627516371 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12864 164 ≤ (458557167 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (91710539 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (91710539 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (89115497 / 62500000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4615780323 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((908817 / 250000000) : ℝ) ≤ √(17 / (100 * 12864) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12864) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1070692177 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7552080381 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12864) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12864) ≤ (27483939 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12864) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12864 * (164 : ℝ) ^ 2 + 26 / (10 * 12864) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12864) : ℝ)) (tA 12864 * 164 ^ 2 + 26 / (10 * 12864)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((908817 / 250000000))) * ((91710539 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((908817 / 250000000)) ^ 3) * ((89115497 / 62500000000000000000000))) + ((4615780323 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((908817 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12864) : ℝ)) d.D d.V d.P (√(tA 12864) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((908817 / 250000000)) ^ 2 * (((1070692177 / 500000000000000)) * ((7552080381 / 200000000000000000)))) + ((4615780323 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12864) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((908817 / 250000000)) * ((91710539 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12864) : ℝ)) (tA 12864 * 164 ^ 2 + 26 / (10 * 12864)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((91710539 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((908817 / 250000000)) ^ 2) * ((89115497 / 62500000000000000000000)) + ((4615780323 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12864) : ℝ)) (√(26 / (10 * 12864) : ℝ)) d.D d.V d.P (√(tA 12864) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((908817 / 250000000)) * (((1070692177 / 500000000000000)) * ((7552080381 / 200000000000000000))) + ((4615780323 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12864) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((91710539 / 20000000000000000000) : ℝ) + ((4615780323 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12864

namespace BstLean.Part266.Row12864
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12864 164 ∧
    0 ≤ (tableEnvelope C).f1 12864 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12864 164 ∧
    0 ≤ (tableEnvelope C).w1 12864 164 ∧ 0 ≤ (tableEnvelope C).w2 12864 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12864 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12864 164 ∧ 0 ≤ d.f1 12864 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12864 164 ∧ 0 ≤ d.w1 12864 164 ∧ 0 ≤ d.w2 12864 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12864 ≤ 2 * (228 / 100 : ℝ) / 12864 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12864 ≤ 2 * (370 / 100 : ℝ) / 12864 := by
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
    (completeRAData (tableEnvelope C) 12864 164).locationBound 12864 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12864 164).energyBound 12864 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12864 164) (d.f1 12864 164) d.f2 ≤
      32 * (((4438026231 / 1000000000000000000) : ℝ) + (296120161 / 200000000000000000) + (355862997 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12864 164) (d.w1 12864 164)
      (d.w2 12864 164) ≤
      32 * (((881986209 / 50000000000000000000) : ℝ) + (627516371 / 50000000000000000000) + (458557167 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12864 164) (d.f1 12864 164) d.f2 ≤
      ((4438026231 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4438026231 / 1000000000000000000)) * ((296120161 / 200000000000000000)) * (126 / 100) +
      2 * (((296120161 / 200000000000000000)) ^ 2 + 2 * ((4438026231 / 1000000000000000000)) * ((355862997 / 1000000000000000000))) +
      6 * ((296120161 / 200000000000000000)) * ((355862997 / 1000000000000000000)) * (126 / 100) + 8 * ((355862997 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12864 164) (d.f1 12864 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12864 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12864 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12864 164) (d.f1 12864 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12864 164) (d.w1 12864 164) (d.w2 12864 164)
  have hwexpr0 : 0 ≤ d.w0 12864 164 + d.w1 12864 164 * √(π / 2) +
      2 * d.w2 12864 164 + energyR16 12864 *
      radiusPolynomialRoot16 (d.w0 12864 164) (d.w1 12864 164) (d.w2 12864 164) := by
    positivity
  constructor
  · change (12864 : ℝ) ^ 8 * (mA 12864 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12864 164) (d.f1 12864 164) d.f2 + locationR16 12864 *
        radiusPolynomialRoot16 (d.f0 12864 164) (d.f1 12864 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12864 : ℝ) ^ 8 * (mA 12864 : ℝ) ^ 8 *
        ((((4438026231 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4438026231 / 1000000000000000000)) * ((296120161 / 200000000000000000)) * (126 / 100) +
          2 * (((296120161 / 200000000000000000)) ^ 2 + 2 * ((4438026231 / 1000000000000000000)) * ((355862997 / 1000000000000000000))) +
          6 * ((296120161 / 200000000000000000)) * ((355862997 / 1000000000000000000)) * (126 / 100) + 8 * ((355862997 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12864) *
          (32 * (((4438026231 / 1000000000000000000) : ℝ) + (296120161 / 200000000000000000) + (355862997 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12864 : ℝ) ^ 16 *
      (d.w0 12864 164 + d.w1 12864 164 * √(π / 2) + 2 * d.w2 12864 164 +
        energyR16 12864 * radiusPolynomialRoot16 (d.w0 12864 164) (d.w1 12864 164)
          (d.w2 12864 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12864 : ℝ) ^ 16 *
        (((881986209 / 50000000000000000000) : ℝ) + ((627516371 / 50000000000000000000)) * (126 / 100) + 2 * ((458557167 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12864) *
          (32 * (((881986209 / 50000000000000000000) : ℝ) + (627516371 / 50000000000000000000) + (458557167 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12864

/-! A coarse bound on the actual paper statistics constant at dimension 12865. -/
namespace BstLean.Part266.Row12865
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12863 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12863 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12863 128 ≤ (13117 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13117 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12865) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12865 : ℕ))
    (by norm_num : (12865 : ℕ) ≤ 16384)
  have ht : paperTail256 12865 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12865 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12865 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12865 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12865 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12865 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12863 128 * √(2 / (12865 : ℝ)) *
      (√(12865 : ℝ) + paperT0 12865 + paperTail256 12865) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12865 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12865 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12865 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12863 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12863 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12865 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12865

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12865
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12865 (61 / 100) 164 (17 / (100 * 12865)) (26 / (10 * 12865)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12865 (61 / 100) 164 (17 / (100 * 12865)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (458445767 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (71270233 / 50000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (18451533 / 4000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12865 / 12865 * (61 / 100)) ^ 4 * inverseRadius8 (12865 - 1) /
            envelopeGap 12865 (61 / 100) 164 (17 / (100 * 12865)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12865

namespace BstLean.Part266.Row12865
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12865 164 ≤ (4437166313 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12865 164 ≤ (23129901 / 15625000000000000)
  f2 : (tableEnvelope C).f2 ≤ (355793913 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12865 164 ≤ (1763561597 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12865 164 ≤ (313685083 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12865 164 ≤ (114612559 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (458445767 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (458445767 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (71270233 / 50000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (18451533 / 4000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1817563 / 500000000) : ℝ) ≤ √(17 / (100 * 12865) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12865) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2141134669 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37754531649 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12865) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12865) ≤ (109927211 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12865) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12865 * (164 : ℝ) ^ 2 + 26 / (10 * 12865) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12865) : ℝ)) (tA 12865 * 164 ^ 2 + 26 / (10 * 12865)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1817563 / 500000000))) * ((458445767 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1817563 / 500000000)) ^ 3) * ((71270233 / 50000000000000000000000))) + ((18451533 / 4000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1817563 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12865) : ℝ)) d.D d.V d.P (√(tA 12865) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1817563 / 500000000)) ^ 2 * (((2141134669 / 1000000000000000)) * ((37754531649 / 1000000000000000000)))) + ((18451533 / 4000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12865) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1817563 / 500000000)) * ((458445767 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12865) : ℝ)) (tA 12865 * 164 ^ 2 + 26 / (10 * 12865)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((458445767 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1817563 / 500000000)) ^ 2) * ((71270233 / 50000000000000000000000)) + ((18451533 / 4000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12865) : ℝ)) (√(26 / (10 * 12865) : ℝ)) d.D d.V d.P (√(tA 12865) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1817563 / 500000000)) * (((2141134669 / 1000000000000000)) * ((37754531649 / 1000000000000000000))) + ((18451533 / 4000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12865) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((458445767 / 100000000000000000000) : ℝ) + ((18451533 / 4000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12865

namespace BstLean.Part266.Row12865
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12865 164 ∧
    0 ≤ (tableEnvelope C).f1 12865 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12865 164 ∧
    0 ≤ (tableEnvelope C).w1 12865 164 ∧ 0 ≤ (tableEnvelope C).w2 12865 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12865 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12865 164 ∧ 0 ≤ d.f1 12865 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12865 164 ∧ 0 ≤ d.w1 12865 164 ∧ 0 ≤ d.w2 12865 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12865 ≤ 2 * (228 / 100 : ℝ) / 12865 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12865 ≤ 2 * (370 / 100 : ℝ) / 12865 := by
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
    (completeRAData (tableEnvelope C) 12865 164).locationBound 12865 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12865 164).energyBound 12865 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12865 164) (d.f1 12865 164) d.f2 ≤
      32 * (((4437166313 / 1000000000000000000) : ℝ) + (23129901 / 15625000000000000) + (355793913 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12865 164) (d.w1 12865 164)
      (d.w2 12865 164) ≤
      32 * (((1763561597 / 100000000000000000000) : ℝ) + (313685083 / 25000000000000000000) + (114612559 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12865 164) (d.f1 12865 164) d.f2 ≤
      ((4437166313 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4437166313 / 1000000000000000000)) * ((23129901 / 15625000000000000)) * (126 / 100) +
      2 * (((23129901 / 15625000000000000)) ^ 2 + 2 * ((4437166313 / 1000000000000000000)) * ((355793913 / 1000000000000000000))) +
      6 * ((23129901 / 15625000000000000)) * ((355793913 / 1000000000000000000)) * (126 / 100) + 8 * ((355793913 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12865 164) (d.f1 12865 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12865 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12865 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12865 164) (d.f1 12865 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12865 164) (d.w1 12865 164) (d.w2 12865 164)
  have hwexpr0 : 0 ≤ d.w0 12865 164 + d.w1 12865 164 * √(π / 2) +
      2 * d.w2 12865 164 + energyR16 12865 *
      radiusPolynomialRoot16 (d.w0 12865 164) (d.w1 12865 164) (d.w2 12865 164) := by
    positivity
  constructor
  · change (12865 : ℝ) ^ 8 * (mA 12865 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12865 164) (d.f1 12865 164) d.f2 + locationR16 12865 *
        radiusPolynomialRoot16 (d.f0 12865 164) (d.f1 12865 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12865 : ℝ) ^ 8 * (mA 12865 : ℝ) ^ 8 *
        ((((4437166313 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4437166313 / 1000000000000000000)) * ((23129901 / 15625000000000000)) * (126 / 100) +
          2 * (((23129901 / 15625000000000000)) ^ 2 + 2 * ((4437166313 / 1000000000000000000)) * ((355793913 / 1000000000000000000))) +
          6 * ((23129901 / 15625000000000000)) * ((355793913 / 1000000000000000000)) * (126 / 100) + 8 * ((355793913 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12865) *
          (32 * (((4437166313 / 1000000000000000000) : ℝ) + (23129901 / 15625000000000000) + (355793913 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12865 : ℝ) ^ 16 *
      (d.w0 12865 164 + d.w1 12865 164 * √(π / 2) + 2 * d.w2 12865 164 +
        energyR16 12865 * radiusPolynomialRoot16 (d.w0 12865 164) (d.w1 12865 164)
          (d.w2 12865 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12865 : ℝ) ^ 16 *
        (((1763561597 / 100000000000000000000) : ℝ) + ((313685083 / 25000000000000000000)) * (126 / 100) + 2 * ((114612559 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12865) *
          (32 * (((1763561597 / 100000000000000000000) : ℝ) + (313685083 / 25000000000000000000) + (114612559 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12865

/-! A coarse bound on the actual paper statistics constant at dimension 12866. -/
namespace BstLean.Part266.Row12866
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12864 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12864 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12864 128 ≤ (13118 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13118 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12866) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12866 : ℕ))
    (by norm_num : (12866 : ℕ) ≤ 16384)
  have ht : paperTail256 12866 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12866 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12866 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12866 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12866 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12866 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12864 128 * √(2 / (12866 : ℝ)) *
      (√(12866 : ℝ) + paperT0 12866 + paperTail256 12866) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12866 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12866 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12866 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12864 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12864 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12866 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12866

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12866
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12866 (61 / 100) 164 (17 / (100 * 12866)) (26 / (10 * 12866)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12866 (61 / 100) 164 (17 / (100 * 12866)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (458338873 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (71248077 / 50000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (184399529 / 40000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12866 / 12866 * (61 / 100)) ^ 4 * inverseRadius8 (12866 - 1) /
            envelopeGap 12866 (61 / 100) 164 (17 / (100 * 12866)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12866

namespace BstLean.Part266.Row12866
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12866 164 ≤ (1109075791 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12866 164 ≤ (740012901 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (22232797 / 62500000000000000)
  w0 : (tableEnvelope C).w0 12866 164 ≤ (1763150197 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12866 164 ≤ (50177907 / 4000000000000000000)
  w2 : (tableEnvelope C).w2 12866 164 ≤ (458343339 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (458338873 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (458338873 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (71248077 / 50000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (184399529 / 40000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((726997 / 200000000) : ℝ) ≤ √(17 / (100 * 12866) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12866) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (428177007 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18874331379 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12866) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12866) ≤ (109918667 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12866) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12866 * (164 : ℝ) ^ 2 + 26 / (10 * 12866) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12866) : ℝ)) (tA 12866 * 164 ^ 2 + 26 / (10 * 12866)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((726997 / 200000000))) * ((458338873 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((726997 / 200000000)) ^ 3) * ((71248077 / 50000000000000000000000))) + ((184399529 / 40000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((726997 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12866) : ℝ)) d.D d.V d.P (√(tA 12866) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((726997 / 200000000)) ^ 2 * (((428177007 / 200000000000000)) * ((18874331379 / 500000000000000000)))) + ((184399529 / 40000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12866) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((726997 / 200000000)) * ((458338873 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12866) : ℝ)) (tA 12866 * 164 ^ 2 + 26 / (10 * 12866)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((458338873 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((726997 / 200000000)) ^ 2) * ((71248077 / 50000000000000000000000)) + ((184399529 / 40000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12866) : ℝ)) (√(26 / (10 * 12866) : ℝ)) d.D d.V d.P (√(tA 12866) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((726997 / 200000000)) * (((428177007 / 200000000000000)) * ((18874331379 / 500000000000000000))) + ((184399529 / 40000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12866) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((458338873 / 100000000000000000000) : ℝ) + ((184399529 / 40000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12866

namespace BstLean.Part266.Row12866
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12866 164 ∧
    0 ≤ (tableEnvelope C).f1 12866 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12866 164 ∧
    0 ≤ (tableEnvelope C).w1 12866 164 ∧ 0 ≤ (tableEnvelope C).w2 12866 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12866 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12866 164 ∧ 0 ≤ d.f1 12866 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12866 164 ∧ 0 ≤ d.w1 12866 164 ∧ 0 ≤ d.w2 12866 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12866 ≤ 2 * (228 / 100 : ℝ) / 12866 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12866 ≤ 2 * (370 / 100 : ℝ) / 12866 := by
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
    (completeRAData (tableEnvelope C) 12866 164).locationBound 12866 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12866 164).energyBound 12866 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12866 164) (d.f1 12866 164) d.f2 ≤
      32 * (((1109075791 / 250000000000000000) : ℝ) + (740012901 / 500000000000000000) + (22232797 / 62500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12866 164) (d.w1 12866 164)
      (d.w2 12866 164) ≤
      32 * (((1763150197 / 100000000000000000000) : ℝ) + (50177907 / 4000000000000000000) + (458343339 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12866 164) (d.f1 12866 164) d.f2 ≤
      ((1109075791 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1109075791 / 250000000000000000)) * ((740012901 / 500000000000000000)) * (126 / 100) +
      2 * (((740012901 / 500000000000000000)) ^ 2 + 2 * ((1109075791 / 250000000000000000)) * ((22232797 / 62500000000000000))) +
      6 * ((740012901 / 500000000000000000)) * ((22232797 / 62500000000000000)) * (126 / 100) + 8 * ((22232797 / 62500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12866 164) (d.f1 12866 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12866 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12866 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12866 164) (d.f1 12866 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12866 164) (d.w1 12866 164) (d.w2 12866 164)
  have hwexpr0 : 0 ≤ d.w0 12866 164 + d.w1 12866 164 * √(π / 2) +
      2 * d.w2 12866 164 + energyR16 12866 *
      radiusPolynomialRoot16 (d.w0 12866 164) (d.w1 12866 164) (d.w2 12866 164) := by
    positivity
  constructor
  · change (12866 : ℝ) ^ 8 * (mA 12866 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12866 164) (d.f1 12866 164) d.f2 + locationR16 12866 *
        radiusPolynomialRoot16 (d.f0 12866 164) (d.f1 12866 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12866 : ℝ) ^ 8 * (mA 12866 : ℝ) ^ 8 *
        ((((1109075791 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1109075791 / 250000000000000000)) * ((740012901 / 500000000000000000)) * (126 / 100) +
          2 * (((740012901 / 500000000000000000)) ^ 2 + 2 * ((1109075791 / 250000000000000000)) * ((22232797 / 62500000000000000))) +
          6 * ((740012901 / 500000000000000000)) * ((22232797 / 62500000000000000)) * (126 / 100) + 8 * ((22232797 / 62500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12866) *
          (32 * (((1109075791 / 250000000000000000) : ℝ) + (740012901 / 500000000000000000) + (22232797 / 62500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12866 : ℝ) ^ 16 *
      (d.w0 12866 164 + d.w1 12866 164 * √(π / 2) + 2 * d.w2 12866 164 +
        energyR16 12866 * radiusPolynomialRoot16 (d.w0 12866 164) (d.w1 12866 164)
          (d.w2 12866 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12866 : ℝ) ^ 16 *
        (((1763150197 / 100000000000000000000) : ℝ) + ((50177907 / 4000000000000000000)) * (126 / 100) + 2 * ((458343339 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12866) *
          (32 * (((1763150197 / 100000000000000000000) : ℝ) + (50177907 / 4000000000000000000) + (458343339 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12866

/-! A coarse bound on the actual paper statistics constant at dimension 12867. -/
namespace BstLean.Part266.Row12867
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12865 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12865 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12865 128 ≤ (13119 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13119 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12867) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12867 : ℕ))
    (by norm_num : (12867 : ℕ) ≤ 16384)
  have ht : paperTail256 12867 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12867 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12867 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12867 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12867 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12867 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12865 128 * √(2 / (12867 : ℝ)) *
      (√(12867 : ℝ) + paperT0 12867 + paperTail256 12867) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12867 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12867 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12867 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12865 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12865 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12867 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12867

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12867
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12867 (61 / 100) 164 (17 / (100 * 12867)) (26 / (10 * 12867)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12867 (61 / 100) 164 (17 / (100 * 12867)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (114558003 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1424518593 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2303547623 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12867 / 12867 * (61 / 100)) ^ 4 * inverseRadius8 (12867 - 1) /
            envelopeGap 12867 (61 / 100) 164 (17 / (100 * 12867)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12867

namespace BstLean.Part266.Row12867
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12867 164 ≤ (4435440309 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12867 164 ≤ (147973803 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (355655611 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12867 164 ≤ (881369469 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12867 164 ≤ (627077557 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12867 164 ≤ (18329459 / 4000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (114558003 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (114558003 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1424518593 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2303547623 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((908711 / 250000000) : ℝ) ≤ √(17 / (100 * 12867) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12867) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (267579431 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37742795247 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12867) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12867) ≤ (27477531 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12867) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12867 * (164 : ℝ) ^ 2 + 26 / (10 * 12867) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12867) : ℝ)) (tA 12867 * 164 ^ 2 + 26 / (10 * 12867)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((908711 / 250000000))) * ((114558003 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((908711 / 250000000)) ^ 3) * ((1424518593 / 1000000000000000000000000))) + ((2303547623 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((908711 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12867) : ℝ)) d.D d.V d.P (√(tA 12867) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((908711 / 250000000)) ^ 2 * (((267579431 / 125000000000000)) * ((37742795247 / 1000000000000000000)))) + ((2303547623 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12867) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((908711 / 250000000)) * ((114558003 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12867) : ℝ)) (tA 12867 * 164 ^ 2 + 26 / (10 * 12867)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((114558003 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((908711 / 250000000)) ^ 2) * ((1424518593 / 1000000000000000000000000)) + ((2303547623 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12867) : ℝ)) (√(26 / (10 * 12867) : ℝ)) d.D d.V d.P (√(tA 12867) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((908711 / 250000000)) * (((267579431 / 125000000000000)) * ((37742795247 / 1000000000000000000))) + ((2303547623 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12867) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((114558003 / 25000000000000000000) : ℝ) + ((2303547623 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12867

namespace BstLean.Part266.Row12867
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12867 164 ∧
    0 ≤ (tableEnvelope C).f1 12867 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12867 164 ∧
    0 ≤ (tableEnvelope C).w1 12867 164 ∧ 0 ≤ (tableEnvelope C).w2 12867 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12867 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12867 164 ∧ 0 ≤ d.f1 12867 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12867 164 ∧ 0 ≤ d.w1 12867 164 ∧ 0 ≤ d.w2 12867 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12867 ≤ 2 * (228 / 100 : ℝ) / 12867 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12867 ≤ 2 * (370 / 100 : ℝ) / 12867 := by
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
    (completeRAData (tableEnvelope C) 12867 164).locationBound 12867 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12867 164).energyBound 12867 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12867 164) (d.f1 12867 164) d.f2 ≤
      32 * (((4435440309 / 1000000000000000000) : ℝ) + (147973803 / 100000000000000000) + (355655611 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12867 164) (d.w1 12867 164)
      (d.w2 12867 164) ≤
      32 * (((881369469 / 50000000000000000000) : ℝ) + (627077557 / 50000000000000000000) + (18329459 / 4000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12867 164) (d.f1 12867 164) d.f2 ≤
      ((4435440309 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4435440309 / 1000000000000000000)) * ((147973803 / 100000000000000000)) * (126 / 100) +
      2 * (((147973803 / 100000000000000000)) ^ 2 + 2 * ((4435440309 / 1000000000000000000)) * ((355655611 / 1000000000000000000))) +
      6 * ((147973803 / 100000000000000000)) * ((355655611 / 1000000000000000000)) * (126 / 100) + 8 * ((355655611 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12867 164) (d.f1 12867 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12867 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12867 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12867 164) (d.f1 12867 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12867 164) (d.w1 12867 164) (d.w2 12867 164)
  have hwexpr0 : 0 ≤ d.w0 12867 164 + d.w1 12867 164 * √(π / 2) +
      2 * d.w2 12867 164 + energyR16 12867 *
      radiusPolynomialRoot16 (d.w0 12867 164) (d.w1 12867 164) (d.w2 12867 164) := by
    positivity
  constructor
  · change (12867 : ℝ) ^ 8 * (mA 12867 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12867 164) (d.f1 12867 164) d.f2 + locationR16 12867 *
        radiusPolynomialRoot16 (d.f0 12867 164) (d.f1 12867 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12867 : ℝ) ^ 8 * (mA 12867 : ℝ) ^ 8 *
        ((((4435440309 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4435440309 / 1000000000000000000)) * ((147973803 / 100000000000000000)) * (126 / 100) +
          2 * (((147973803 / 100000000000000000)) ^ 2 + 2 * ((4435440309 / 1000000000000000000)) * ((355655611 / 1000000000000000000))) +
          6 * ((147973803 / 100000000000000000)) * ((355655611 / 1000000000000000000)) * (126 / 100) + 8 * ((355655611 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12867) *
          (32 * (((4435440309 / 1000000000000000000) : ℝ) + (147973803 / 100000000000000000) + (355655611 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12867 : ℝ) ^ 16 *
      (d.w0 12867 164 + d.w1 12867 164 * √(π / 2) + 2 * d.w2 12867 164 +
        energyR16 12867 * radiusPolynomialRoot16 (d.w0 12867 164) (d.w1 12867 164)
          (d.w2 12867 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12867 : ℝ) ^ 16 *
        (((881369469 / 50000000000000000000) : ℝ) + ((627077557 / 50000000000000000000)) * (126 / 100) + 2 * ((18329459 / 4000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12867) *
          (32 * (((881369469 / 50000000000000000000) : ℝ) + (627077557 / 50000000000000000000) + (18329459 / 4000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12867

/-! A coarse bound on the actual paper statistics constant at dimension 12868. -/
namespace BstLean.Part266.Row12868
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12866 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12866 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12866 128 ≤ (13120 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13120 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12868) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12868 : ℕ))
    (by norm_num : (12868 : ℕ) ≤ 16384)
  have ht : paperTail256 12868 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12868 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12868 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12868 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12868 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12868 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12866 128 * √(2 / (12868 : ℝ)) *
      (√(12868 : ℝ) + paperT0 12868 + paperTail256 12868) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12868 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12868 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12868 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12866 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12866 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12868 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12868

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12868
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12868 (61 / 100) 164 (17 / (100 * 12868)) (26 / (10 * 12868)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12868 (61 / 100) 164 (17 / (100 * 12868)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (3579103 / 781250000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (712037909 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4604204311 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12868 / 12868 * (61 / 100)) ^ 4 * inverseRadius8 (12868 - 1) /
            envelopeGap 12868 (61 / 100) 164 (17 / (100 * 12868)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12868

namespace BstLean.Part266.Row12868
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12868 164 ≤ (4434577747 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12868 164 ≤ (1479450351 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (35558649 / 100000000000000000)
  w0 : (tableEnvelope C).w0 12868 164 ≤ (1762327819 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12868 164 ≤ (25077253 / 2000000000000000000)
  w2 : (tableEnvelope C).w2 12868 164 ≤ (91625929 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (3579103 / 781250000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (3579103 / 781250000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (712037909 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4604204311 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3634703 / 1000000000) : ℝ) ≤ √(17 / (100 * 12868) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12868) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (214038591 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18868464551 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12868) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12868) ≤ (109901583 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12868) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12868 * (164 : ℝ) ^ 2 + 26 / (10 * 12868) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12868) : ℝ)) (tA 12868 * 164 ^ 2 + 26 / (10 * 12868)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3634703 / 1000000000))) * ((3579103 / 781250000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3634703 / 1000000000)) ^ 3) * ((712037909 / 500000000000000000000000))) + ((4604204311 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3634703 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12868) : ℝ)) d.D d.V d.P (√(tA 12868) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3634703 / 1000000000)) ^ 2 * (((214038591 / 100000000000000)) * ((18868464551 / 500000000000000000)))) + ((4604204311 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12868) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3634703 / 1000000000)) * ((3579103 / 781250000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12868) : ℝ)) (tA 12868 * 164 ^ 2 + 26 / (10 * 12868)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((3579103 / 781250000000000000) : ℝ) + (24198 / 100000) / (2 * ((3634703 / 1000000000)) ^ 2) * ((712037909 / 500000000000000000000000)) + ((4604204311 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12868) : ℝ)) (√(26 / (10 * 12868) : ℝ)) d.D d.V d.P (√(tA 12868) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3634703 / 1000000000)) * (((214038591 / 100000000000000)) * ((18868464551 / 500000000000000000))) + ((4604204311 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12868) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((3579103 / 781250000000000000) : ℝ) + ((4604204311 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12868

namespace BstLean.Part266.Row12868
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12868 164 ∧
    0 ≤ (tableEnvelope C).f1 12868 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12868 164 ∧
    0 ≤ (tableEnvelope C).w1 12868 164 ∧ 0 ≤ (tableEnvelope C).w2 12868 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12868 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12868 164 ∧ 0 ≤ d.f1 12868 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12868 164 ∧ 0 ≤ d.w1 12868 164 ∧ 0 ≤ d.w2 12868 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12868 ≤ 2 * (228 / 100 : ℝ) / 12868 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12868 ≤ 2 * (370 / 100 : ℝ) / 12868 := by
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
    (completeRAData (tableEnvelope C) 12868 164).locationBound 12868 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12868 164).energyBound 12868 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12868 164) (d.f1 12868 164) d.f2 ≤
      32 * (((4434577747 / 1000000000000000000) : ℝ) + (1479450351 / 1000000000000000000) + (35558649 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12868 164) (d.w1 12868 164)
      (d.w2 12868 164) ≤
      32 * (((1762327819 / 100000000000000000000) : ℝ) + (25077253 / 2000000000000000000) + (91625929 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12868 164) (d.f1 12868 164) d.f2 ≤
      ((4434577747 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4434577747 / 1000000000000000000)) * ((1479450351 / 1000000000000000000)) * (126 / 100) +
      2 * (((1479450351 / 1000000000000000000)) ^ 2 + 2 * ((4434577747 / 1000000000000000000)) * ((35558649 / 100000000000000000))) +
      6 * ((1479450351 / 1000000000000000000)) * ((35558649 / 100000000000000000)) * (126 / 100) + 8 * ((35558649 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12868 164) (d.f1 12868 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12868 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12868 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12868 164) (d.f1 12868 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12868 164) (d.w1 12868 164) (d.w2 12868 164)
  have hwexpr0 : 0 ≤ d.w0 12868 164 + d.w1 12868 164 * √(π / 2) +
      2 * d.w2 12868 164 + energyR16 12868 *
      radiusPolynomialRoot16 (d.w0 12868 164) (d.w1 12868 164) (d.w2 12868 164) := by
    positivity
  constructor
  · change (12868 : ℝ) ^ 8 * (mA 12868 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12868 164) (d.f1 12868 164) d.f2 + locationR16 12868 *
        radiusPolynomialRoot16 (d.f0 12868 164) (d.f1 12868 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12868 : ℝ) ^ 8 * (mA 12868 : ℝ) ^ 8 *
        ((((4434577747 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4434577747 / 1000000000000000000)) * ((1479450351 / 1000000000000000000)) * (126 / 100) +
          2 * (((1479450351 / 1000000000000000000)) ^ 2 + 2 * ((4434577747 / 1000000000000000000)) * ((35558649 / 100000000000000000))) +
          6 * ((1479450351 / 1000000000000000000)) * ((35558649 / 100000000000000000)) * (126 / 100) + 8 * ((35558649 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12868) *
          (32 * (((4434577747 / 1000000000000000000) : ℝ) + (1479450351 / 1000000000000000000) + (35558649 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12868 : ℝ) ^ 16 *
      (d.w0 12868 164 + d.w1 12868 164 * √(π / 2) + 2 * d.w2 12868 164 +
        energyR16 12868 * radiusPolynomialRoot16 (d.w0 12868 164) (d.w1 12868 164)
          (d.w2 12868 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12868 : ℝ) ^ 16 *
        (((1762327819 / 100000000000000000000) : ℝ) + ((25077253 / 2000000000000000000)) * (126 / 100) + 2 * ((91625929 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12868) *
          (32 * (((1762327819 / 100000000000000000000) : ℝ) + (25077253 / 2000000000000000000) + (91625929 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12868

/-! A coarse bound on the actual paper statistics constant at dimension 12869. -/
namespace BstLean.Part266.Row12869
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12867 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12867 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12867 128 ≤ (13121 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13121 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12869) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12869 : ℕ))
    (by norm_num : (12869 : ℕ) ≤ 16384)
  have ht : paperTail256 12869 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12869 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12869 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12869 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12869 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12869 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12867 128 * √(2 / (12869 : ℝ)) *
      (√(12869 : ℝ) + paperT0 12869 + paperTail256 12869) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12869 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12869 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12869 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12867 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12867 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12869 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12869

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12869
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12869 (61 / 100) 164 (17 / (100 * 12869)) (26 / (10 * 12869)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12869 (61 / 100) 164 (17 / (100 * 12869)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (45801839 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (284726643 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4601315419 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12869 / 12869 * (61 / 100)) ^ 4 * inverseRadius8 (12869 - 1) /
            envelopeGap 12869 (61 / 100) 164 (17 / (100 * 12869)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12869

namespace BstLean.Part266.Row12869
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12869 164 ≤ (4433719 / 1000000000000000)
  f1 : (tableEnvelope C).f1 12869 164 ≤ (1479163577 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (355517489 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12869 164 ≤ (1761917557 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12869 164 ≤ (313392657 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12869 164 ≤ (7156607 / 1562500000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (45801839 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (45801839 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (284726643 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4601315419 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3634561 / 1000000000) : ℝ) ≤ √(17 / (100 * 12869) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12869) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2140136421 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9432766081 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12869) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12869) ≤ (109893043 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12869) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12869 * (164 : ℝ) ^ 2 + 26 / (10 * 12869) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12869) : ℝ)) (tA 12869 * 164 ^ 2 + 26 / (10 * 12869)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3634561 / 1000000000))) * ((45801839 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3634561 / 1000000000)) ^ 3) * ((284726643 / 200000000000000000000000))) + ((4601315419 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3634561 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12869) : ℝ)) d.D d.V d.P (√(tA 12869) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3634561 / 1000000000)) ^ 2 * (((2140136421 / 1000000000000000)) * ((9432766081 / 250000000000000000)))) + ((4601315419 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12869) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3634561 / 1000000000)) * ((45801839 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12869) : ℝ)) (tA 12869 * 164 ^ 2 + 26 / (10 * 12869)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((45801839 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3634561 / 1000000000)) ^ 2) * ((284726643 / 200000000000000000000000)) + ((4601315419 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12869) : ℝ)) (√(26 / (10 * 12869) : ℝ)) d.D d.V d.P (√(tA 12869) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3634561 / 1000000000)) * (((2140136421 / 1000000000000000)) * ((9432766081 / 250000000000000000))) + ((4601315419 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12869) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((45801839 / 10000000000000000000) : ℝ) + ((4601315419 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12869

namespace BstLean.Part266.Row12869
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12869 164 ∧
    0 ≤ (tableEnvelope C).f1 12869 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12869 164 ∧
    0 ≤ (tableEnvelope C).w1 12869 164 ∧ 0 ≤ (tableEnvelope C).w2 12869 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12869 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12869 164 ∧ 0 ≤ d.f1 12869 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12869 164 ∧ 0 ≤ d.w1 12869 164 ∧ 0 ≤ d.w2 12869 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12869 ≤ 2 * (228 / 100 : ℝ) / 12869 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12869 ≤ 2 * (370 / 100 : ℝ) / 12869 := by
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
    (completeRAData (tableEnvelope C) 12869 164).locationBound 12869 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12869 164).energyBound 12869 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12869 164) (d.f1 12869 164) d.f2 ≤
      32 * (((4433719 / 1000000000000000) : ℝ) + (1479163577 / 1000000000000000000) + (355517489 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12869 164) (d.w1 12869 164)
      (d.w2 12869 164) ≤
      32 * (((1761917557 / 100000000000000000000) : ℝ) + (313392657 / 25000000000000000000) + (7156607 / 1562500000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12869 164) (d.f1 12869 164) d.f2 ≤
      ((4433719 / 1000000000000000) : ℝ) ^ 2 + 2 * ((4433719 / 1000000000000000)) * ((1479163577 / 1000000000000000000)) * (126 / 100) +
      2 * (((1479163577 / 1000000000000000000)) ^ 2 + 2 * ((4433719 / 1000000000000000)) * ((355517489 / 1000000000000000000))) +
      6 * ((1479163577 / 1000000000000000000)) * ((355517489 / 1000000000000000000)) * (126 / 100) + 8 * ((355517489 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12869 164) (d.f1 12869 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12869 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12869 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12869 164) (d.f1 12869 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12869 164) (d.w1 12869 164) (d.w2 12869 164)
  have hwexpr0 : 0 ≤ d.w0 12869 164 + d.w1 12869 164 * √(π / 2) +
      2 * d.w2 12869 164 + energyR16 12869 *
      radiusPolynomialRoot16 (d.w0 12869 164) (d.w1 12869 164) (d.w2 12869 164) := by
    positivity
  constructor
  · change (12869 : ℝ) ^ 8 * (mA 12869 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12869 164) (d.f1 12869 164) d.f2 + locationR16 12869 *
        radiusPolynomialRoot16 (d.f0 12869 164) (d.f1 12869 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12869 : ℝ) ^ 8 * (mA 12869 : ℝ) ^ 8 *
        ((((4433719 / 1000000000000000) : ℝ) ^ 2 + 2 * ((4433719 / 1000000000000000)) * ((1479163577 / 1000000000000000000)) * (126 / 100) +
          2 * (((1479163577 / 1000000000000000000)) ^ 2 + 2 * ((4433719 / 1000000000000000)) * ((355517489 / 1000000000000000000))) +
          6 * ((1479163577 / 1000000000000000000)) * ((355517489 / 1000000000000000000)) * (126 / 100) + 8 * ((355517489 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12869) *
          (32 * (((4433719 / 1000000000000000) : ℝ) + (1479163577 / 1000000000000000000) + (355517489 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12869 : ℝ) ^ 16 *
      (d.w0 12869 164 + d.w1 12869 164 * √(π / 2) + 2 * d.w2 12869 164 +
        energyR16 12869 * radiusPolynomialRoot16 (d.w0 12869 164) (d.w1 12869 164)
          (d.w2 12869 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12869 : ℝ) ^ 16 *
        (((1761917557 / 100000000000000000000) : ℝ) + ((313392657 / 25000000000000000000)) * (126 / 100) + 2 * ((7156607 / 1562500000000000000)) +
          (2 * (370 / 100 : ℝ) / 12869) *
          (32 * (((1761917557 / 100000000000000000000) : ℝ) + (313392657 / 25000000000000000000) + (7156607 / 1562500000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12869

/-! A coarse bound on the actual paper statistics constant at dimension 12870. -/
namespace BstLean.Part266.Row12870
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12868 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12868 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12868 128 ≤ (13122 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13122 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12870) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12870 : ℕ))
    (by norm_num : (12870 : ℕ) ≤ 16384)
  have ht : paperTail256 12870 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12870 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12870 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12870 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12870 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12870 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12868 128 * √(2 / (12870 : ℝ)) *
      (√(12870 : ℝ) + paperT0 12870 + paperTail256 12870) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12870 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12870 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12870 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12868 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12868 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12870 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12870

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12870
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12870 (61 / 100) 164 (17 / (100 * 12870)) (26 / (10 * 12870)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12870 (61 / 100) 164 (17 / (100 * 12870)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (114477907 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1423190783 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (574803571 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12870 / 12870 * (61 / 100)) ^ 4 * inverseRadius8 (12870 - 1) /
            envelopeGap 12870 (61 / 100) 164 (17 / (100 * 12870)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12870

namespace BstLean.Part266.Row12870
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12870 164 ≤ (4432857019 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12870 164 ≤ (18485951 / 12500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (44431051 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12870 164 ≤ (352301343 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12870 164 ≤ (313319589 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12870 164 ≤ (457916083 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (114477907 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (114477907 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1423190783 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (574803571 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((181721 / 50000000) : ℝ) ≤ √(17 / (100 * 12870) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12870) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2139886979 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37725200901 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12870) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12870) ≤ (13735563 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12870) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12870 * (164 : ℝ) ^ 2 + 26 / (10 * 12870) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12870) : ℝ)) (tA 12870 * 164 ^ 2 + 26 / (10 * 12870)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((181721 / 50000000))) * ((114477907 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((181721 / 50000000)) ^ 3) * ((1423190783 / 1000000000000000000000000))) + ((574803571 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((181721 / 50000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12870) : ℝ)) d.D d.V d.P (√(tA 12870) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((181721 / 50000000)) ^ 2 * (((2139886979 / 1000000000000000)) * ((37725200901 / 1000000000000000000)))) + ((574803571 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12870) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((181721 / 50000000)) * ((114477907 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12870) : ℝ)) (tA 12870 * 164 ^ 2 + 26 / (10 * 12870)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((114477907 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((181721 / 50000000)) ^ 2) * ((1423190783 / 1000000000000000000000000)) + ((574803571 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12870) : ℝ)) (√(26 / (10 * 12870) : ℝ)) d.D d.V d.P (√(tA 12870) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((181721 / 50000000)) * (((2139886979 / 1000000000000000)) * ((37725200901 / 1000000000000000000))) + ((574803571 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12870) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((114477907 / 25000000000000000000) : ℝ) + ((574803571 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12870

namespace BstLean.Part266.Row12870
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12870 164 ∧
    0 ≤ (tableEnvelope C).f1 12870 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12870 164 ∧
    0 ≤ (tableEnvelope C).w1 12870 164 ∧ 0 ≤ (tableEnvelope C).w2 12870 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12870 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12870 164 ∧ 0 ≤ d.f1 12870 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12870 164 ∧ 0 ≤ d.w1 12870 164 ∧ 0 ≤ d.w2 12870 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12870 ≤ 2 * (228 / 100 : ℝ) / 12870 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12870 ≤ 2 * (370 / 100 : ℝ) / 12870 := by
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
    (completeRAData (tableEnvelope C) 12870 164).locationBound 12870 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12870 164).energyBound 12870 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12870 164) (d.f1 12870 164) d.f2 ≤
      32 * (((4432857019 / 1000000000000000000) : ℝ) + (18485951 / 12500000000000000) + (44431051 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12870 164) (d.w1 12870 164)
      (d.w2 12870 164) ≤
      32 * (((352301343 / 20000000000000000000) : ℝ) + (313319589 / 25000000000000000000) + (457916083 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12870 164) (d.f1 12870 164) d.f2 ≤
      ((4432857019 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4432857019 / 1000000000000000000)) * ((18485951 / 12500000000000000)) * (126 / 100) +
      2 * (((18485951 / 12500000000000000)) ^ 2 + 2 * ((4432857019 / 1000000000000000000)) * ((44431051 / 125000000000000000))) +
      6 * ((18485951 / 12500000000000000)) * ((44431051 / 125000000000000000)) * (126 / 100) + 8 * ((44431051 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12870 164) (d.f1 12870 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12870 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12870 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12870 164) (d.f1 12870 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12870 164) (d.w1 12870 164) (d.w2 12870 164)
  have hwexpr0 : 0 ≤ d.w0 12870 164 + d.w1 12870 164 * √(π / 2) +
      2 * d.w2 12870 164 + energyR16 12870 *
      radiusPolynomialRoot16 (d.w0 12870 164) (d.w1 12870 164) (d.w2 12870 164) := by
    positivity
  constructor
  · change (12870 : ℝ) ^ 8 * (mA 12870 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12870 164) (d.f1 12870 164) d.f2 + locationR16 12870 *
        radiusPolynomialRoot16 (d.f0 12870 164) (d.f1 12870 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12870 : ℝ) ^ 8 * (mA 12870 : ℝ) ^ 8 *
        ((((4432857019 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4432857019 / 1000000000000000000)) * ((18485951 / 12500000000000000)) * (126 / 100) +
          2 * (((18485951 / 12500000000000000)) ^ 2 + 2 * ((4432857019 / 1000000000000000000)) * ((44431051 / 125000000000000000))) +
          6 * ((18485951 / 12500000000000000)) * ((44431051 / 125000000000000000)) * (126 / 100) + 8 * ((44431051 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12870) *
          (32 * (((4432857019 / 1000000000000000000) : ℝ) + (18485951 / 12500000000000000) + (44431051 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12870 : ℝ) ^ 16 *
      (d.w0 12870 164 + d.w1 12870 164 * √(π / 2) + 2 * d.w2 12870 164 +
        energyR16 12870 * radiusPolynomialRoot16 (d.w0 12870 164) (d.w1 12870 164)
          (d.w2 12870 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12870 : ℝ) ^ 16 *
        (((352301343 / 20000000000000000000) : ℝ) + ((313319589 / 25000000000000000000)) * (126 / 100) + 2 * ((457916083 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12870) *
          (32 * (((352301343 / 20000000000000000000) : ℝ) + (313319589 / 25000000000000000000) + (457916083 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12870

/-! A coarse bound on the actual paper statistics constant at dimension 12871. -/
namespace BstLean.Part266.Row12871
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12869 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12869 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12869 128 ≤ (13123 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13123 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12871) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12871 : ℕ))
    (by norm_num : (12871 : ℕ) ≤ 16384)
  have ht : paperTail256 12871 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12871 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12871 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12871 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12871 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12871 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12869 128 * √(2 / (12871 : ℝ)) *
      (√(12871 : ℝ) + paperT0 12871 + paperTail256 12871) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12871 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12871 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12871 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12869 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12869 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12871 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12871

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12871
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12871 (61 / 100) 164 (17 / (100 * 12871)) (26 / (10 * 12871)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12871 (61 / 100) 164 (17 / (100 * 12871)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (4578049 / 1000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (355687131 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1148885939 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12871 / 12871 * (61 / 100)) ^ 4 * inverseRadius8 (12871 - 1) /
            envelopeGap 12871 (61 / 100) 164 (17 / (100 * 12871)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12871

namespace BstLean.Part266.Row12871
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12871 164 ≤ (886399067 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12871 164 ≤ (369647169 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (355379349 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12871 164 ≤ (352219203 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12871 164 ≤ (626493091 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12871 164 ≤ (57226169 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (4578049 / 1000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (4578049 / 1000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (355687131 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1148885939 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3634279 / 1000000000) : ℝ) ≤ √(17 / (100 * 12871) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12871) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2139637587 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1885966943 / 50000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12871) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12871) ≤ (109875967 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12871) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12871 * (164 : ℝ) ^ 2 + 26 / (10 * 12871) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12871) : ℝ)) (tA 12871 * 164 ^ 2 + 26 / (10 * 12871)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3634279 / 1000000000))) * ((4578049 / 1000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3634279 / 1000000000)) ^ 3) * ((355687131 / 250000000000000000000000))) + ((1148885939 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3634279 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12871) : ℝ)) d.D d.V d.P (√(tA 12871) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3634279 / 1000000000)) ^ 2 * (((2139637587 / 1000000000000000)) * ((1885966943 / 50000000000000000)))) + ((1148885939 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12871) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3634279 / 1000000000)) * ((4578049 / 1000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12871) : ℝ)) (tA 12871 * 164 ^ 2 + 26 / (10 * 12871)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((4578049 / 1000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3634279 / 1000000000)) ^ 2) * ((355687131 / 250000000000000000000000)) + ((1148885939 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12871) : ℝ)) (√(26 / (10 * 12871) : ℝ)) d.D d.V d.P (√(tA 12871) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3634279 / 1000000000)) * (((2139637587 / 1000000000000000)) * ((1885966943 / 50000000000000000))) + ((1148885939 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12871) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((4578049 / 1000000000000000000) : ℝ) + ((1148885939 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12871

namespace BstLean.Part266.Row12871
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12871 164 ∧
    0 ≤ (tableEnvelope C).f1 12871 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12871 164 ∧
    0 ≤ (tableEnvelope C).w1 12871 164 ∧ 0 ≤ (tableEnvelope C).w2 12871 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12871 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12871 164 ∧ 0 ≤ d.f1 12871 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12871 164 ∧ 0 ≤ d.w1 12871 164 ∧ 0 ≤ d.w2 12871 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12871 ≤ 2 * (228 / 100 : ℝ) / 12871 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12871 ≤ 2 * (370 / 100 : ℝ) / 12871 := by
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
    (completeRAData (tableEnvelope C) 12871 164).locationBound 12871 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12871 164).energyBound 12871 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12871 164) (d.f1 12871 164) d.f2 ≤
      32 * (((886399067 / 200000000000000000) : ℝ) + (369647169 / 250000000000000000) + (355379349 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12871 164) (d.w1 12871 164)
      (d.w2 12871 164) ≤
      32 * (((352219203 / 20000000000000000000) : ℝ) + (626493091 / 50000000000000000000) + (57226169 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12871 164) (d.f1 12871 164) d.f2 ≤
      ((886399067 / 200000000000000000) : ℝ) ^ 2 + 2 * ((886399067 / 200000000000000000)) * ((369647169 / 250000000000000000)) * (126 / 100) +
      2 * (((369647169 / 250000000000000000)) ^ 2 + 2 * ((886399067 / 200000000000000000)) * ((355379349 / 1000000000000000000))) +
      6 * ((369647169 / 250000000000000000)) * ((355379349 / 1000000000000000000)) * (126 / 100) + 8 * ((355379349 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12871 164) (d.f1 12871 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12871 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12871 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12871 164) (d.f1 12871 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12871 164) (d.w1 12871 164) (d.w2 12871 164)
  have hwexpr0 : 0 ≤ d.w0 12871 164 + d.w1 12871 164 * √(π / 2) +
      2 * d.w2 12871 164 + energyR16 12871 *
      radiusPolynomialRoot16 (d.w0 12871 164) (d.w1 12871 164) (d.w2 12871 164) := by
    positivity
  constructor
  · change (12871 : ℝ) ^ 8 * (mA 12871 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12871 164) (d.f1 12871 164) d.f2 + locationR16 12871 *
        radiusPolynomialRoot16 (d.f0 12871 164) (d.f1 12871 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12871 : ℝ) ^ 8 * (mA 12871 : ℝ) ^ 8 *
        ((((886399067 / 200000000000000000) : ℝ) ^ 2 + 2 * ((886399067 / 200000000000000000)) * ((369647169 / 250000000000000000)) * (126 / 100) +
          2 * (((369647169 / 250000000000000000)) ^ 2 + 2 * ((886399067 / 200000000000000000)) * ((355379349 / 1000000000000000000))) +
          6 * ((369647169 / 250000000000000000)) * ((355379349 / 1000000000000000000)) * (126 / 100) + 8 * ((355379349 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12871) *
          (32 * (((886399067 / 200000000000000000) : ℝ) + (369647169 / 250000000000000000) + (355379349 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12871 : ℝ) ^ 16 *
      (d.w0 12871 164 + d.w1 12871 164 * √(π / 2) + 2 * d.w2 12871 164 +
        energyR16 12871 * radiusPolynomialRoot16 (d.w0 12871 164) (d.w1 12871 164)
          (d.w2 12871 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12871 : ℝ) ^ 16 *
        (((352219203 / 20000000000000000000) : ℝ) + ((626493091 / 50000000000000000000)) * (126 / 100) + 2 * ((57226169 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12871) *
          (32 * (((352219203 / 20000000000000000000) : ℝ) + (626493091 / 50000000000000000000) + (57226169 / 12500000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12871

/-! A coarse bound on the actual paper statistics constant at dimension 12872. -/
namespace BstLean.Part266.Row12872
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12870 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12870 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12870 128 ≤ (13124 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13124 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12872) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12872 : ℕ))
    (by norm_num : (12872 : ℕ) ≤ 16384)
  have ht : paperTail256 12872 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12872 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12872 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12872 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12872 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12872 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12870 128 * √(2 / (12872 : ℝ)) *
      (√(12872 : ℝ) + paperT0 12872 + paperTail256 12872) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12872 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12872 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12872 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12870 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12870 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12872 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12872

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12872
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12872 (61 / 100) 164 (17 / (100 * 12872)) (26 / (10 * 12872)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12872 (61 / 100) 164 (17 / (100 * 12872)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (91539641 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (355576609 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2296330491 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12872 / 12872 * (61 / 100)) ^ 4 * inverseRadius8 (12872 - 1) /
            envelopeGap 12872 (61 / 100) 164 (17 / (100 * 12872)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12872

namespace BstLean.Part266.Row12872
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12872 164 ≤ (221556697 / 50000000000000000)
  f1 : (tableEnvelope C).f1 12872 164 ≤ (739150681 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (35531031 / 100000000000000000)
  w0 : (tableEnvelope C).w0 12872 164 ≤ (1760685453 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12872 164 ≤ (1252694103 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12872 164 ≤ (228851327 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (91539641 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (91539641 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (355576609 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2296330491 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1817069 / 500000000) : ℝ) ≤ √(17 / (100 * 12872) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12872) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1069694121 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1508539127 / 40000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12872) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12872) ≤ (109867431 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12872) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12872 * (164 : ℝ) ^ 2 + 26 / (10 * 12872) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12872) : ℝ)) (tA 12872 * 164 ^ 2 + 26 / (10 * 12872)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1817069 / 500000000))) * ((91539641 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1817069 / 500000000)) ^ 3) * ((355576609 / 250000000000000000000000))) + ((2296330491 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1817069 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12872) : ℝ)) d.D d.V d.P (√(tA 12872) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1817069 / 500000000)) ^ 2 * (((1069694121 / 500000000000000)) * ((1508539127 / 40000000000000000)))) + ((2296330491 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12872) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1817069 / 500000000)) * ((91539641 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12872) : ℝ)) (tA 12872 * 164 ^ 2 + 26 / (10 * 12872)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((91539641 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1817069 / 500000000)) ^ 2) * ((355576609 / 250000000000000000000000)) + ((2296330491 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12872) : ℝ)) (√(26 / (10 * 12872) : ℝ)) d.D d.V d.P (√(tA 12872) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1817069 / 500000000)) * (((1069694121 / 500000000000000)) * ((1508539127 / 40000000000000000))) + ((2296330491 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12872) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((91539641 / 20000000000000000000) : ℝ) + ((2296330491 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12872

namespace BstLean.Part266.Row12872
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12872 164 ∧
    0 ≤ (tableEnvelope C).f1 12872 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12872 164 ∧
    0 ≤ (tableEnvelope C).w1 12872 164 ∧ 0 ≤ (tableEnvelope C).w2 12872 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12872 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12872 164 ∧ 0 ≤ d.f1 12872 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12872 164 ∧ 0 ≤ d.w1 12872 164 ∧ 0 ≤ d.w2 12872 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12872 ≤ 2 * (228 / 100 : ℝ) / 12872 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12872 ≤ 2 * (370 / 100 : ℝ) / 12872 := by
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
    (completeRAData (tableEnvelope C) 12872 164).locationBound 12872 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12872 164).energyBound 12872 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12872 164) (d.f1 12872 164) d.f2 ≤
      32 * (((221556697 / 50000000000000000) : ℝ) + (739150681 / 500000000000000000) + (35531031 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12872 164) (d.w1 12872 164)
      (d.w2 12872 164) ≤
      32 * (((1760685453 / 100000000000000000000) : ℝ) + (1252694103 / 100000000000000000000) + (228851327 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12872 164) (d.f1 12872 164) d.f2 ≤
      ((221556697 / 50000000000000000) : ℝ) ^ 2 + 2 * ((221556697 / 50000000000000000)) * ((739150681 / 500000000000000000)) * (126 / 100) +
      2 * (((739150681 / 500000000000000000)) ^ 2 + 2 * ((221556697 / 50000000000000000)) * ((35531031 / 100000000000000000))) +
      6 * ((739150681 / 500000000000000000)) * ((35531031 / 100000000000000000)) * (126 / 100) + 8 * ((35531031 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12872 164) (d.f1 12872 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12872 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12872 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12872 164) (d.f1 12872 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12872 164) (d.w1 12872 164) (d.w2 12872 164)
  have hwexpr0 : 0 ≤ d.w0 12872 164 + d.w1 12872 164 * √(π / 2) +
      2 * d.w2 12872 164 + energyR16 12872 *
      radiusPolynomialRoot16 (d.w0 12872 164) (d.w1 12872 164) (d.w2 12872 164) := by
    positivity
  constructor
  · change (12872 : ℝ) ^ 8 * (mA 12872 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12872 164) (d.f1 12872 164) d.f2 + locationR16 12872 *
        radiusPolynomialRoot16 (d.f0 12872 164) (d.f1 12872 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12872 : ℝ) ^ 8 * (mA 12872 : ℝ) ^ 8 *
        ((((221556697 / 50000000000000000) : ℝ) ^ 2 + 2 * ((221556697 / 50000000000000000)) * ((739150681 / 500000000000000000)) * (126 / 100) +
          2 * (((739150681 / 500000000000000000)) ^ 2 + 2 * ((221556697 / 50000000000000000)) * ((35531031 / 100000000000000000))) +
          6 * ((739150681 / 500000000000000000)) * ((35531031 / 100000000000000000)) * (126 / 100) + 8 * ((35531031 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12872) *
          (32 * (((221556697 / 50000000000000000) : ℝ) + (739150681 / 500000000000000000) + (35531031 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12872 : ℝ) ^ 16 *
      (d.w0 12872 164 + d.w1 12872 164 * √(π / 2) + 2 * d.w2 12872 164 +
        energyR16 12872 * radiusPolynomialRoot16 (d.w0 12872 164) (d.w1 12872 164)
          (d.w2 12872 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12872 : ℝ) ^ 16 *
        (((1760685453 / 100000000000000000000) : ℝ) + ((1252694103 / 100000000000000000000)) * (126 / 100) + 2 * ((228851327 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12872) *
          (32 * (((1760685453 / 100000000000000000000) : ℝ) + (1252694103 / 100000000000000000000) + (228851327 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12872

/-! A coarse bound on the actual paper statistics constant at dimension 12873. -/
namespace BstLean.Part266.Row12873
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12871 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12871 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12871 128 ≤ (13125 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13125 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12873) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12873 : ℕ))
    (by norm_num : (12873 : ℕ) ≤ 16384)
  have ht : paperTail256 12873 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12873 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12873 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12873 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12873 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12873 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12871 128 * √(2 / (12873 : ℝ)) *
      (√(12873 : ℝ) + paperT0 12873 + paperTail256 12873) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12873 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12873 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12873 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12871 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12871 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12873 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12873

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12873
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12873 (61 / 100) 164 (17 / (100 * 12873)) (26 / (10 * 12873)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12873 (61 / 100) 164 (17 / (100 * 12873)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (457591543 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (35546613 / 25000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (917956049 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12873 / 12873 * (61 / 100)) ^ 4 * inverseRadius8 (12873 - 1) /
            envelopeGap 12873 (61 / 100) 164 (17 / (100 * 12873)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12873

namespace BstLean.Part266.Row12873
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12873 164 ≤ (4430272839 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12873 164 ≤ (73900707 / 50000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (88810323 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12873 164 ≤ (176027503 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12873 164 ≤ (1252402121 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12873 164 ≤ (45759599 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (457591543 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (457591543 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (35546613 / 25000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (917956049 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3633997 / 1000000000) : ℝ) ≤ √(17 / (100 * 12873) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12873) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1069569473 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (37707618859 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12873) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12873) ≤ (6866181 / 62500000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12873) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12873 * (164 : ℝ) ^ 2 + 26 / (10 * 12873) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12873) : ℝ)) (tA 12873 * 164 ^ 2 + 26 / (10 * 12873)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3633997 / 1000000000))) * ((457591543 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3633997 / 1000000000)) ^ 3) * ((35546613 / 25000000000000000000000))) + ((917956049 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3633997 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12873) : ℝ)) d.D d.V d.P (√(tA 12873) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3633997 / 1000000000)) ^ 2 * (((1069569473 / 500000000000000)) * ((37707618859 / 1000000000000000000)))) + ((917956049 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12873) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3633997 / 1000000000)) * ((457591543 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12873) : ℝ)) (tA 12873 * 164 ^ 2 + 26 / (10 * 12873)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((457591543 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3633997 / 1000000000)) ^ 2) * ((35546613 / 25000000000000000000000)) + ((917956049 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12873) : ℝ)) (√(26 / (10 * 12873) : ℝ)) d.D d.V d.P (√(tA 12873) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3633997 / 1000000000)) * (((1069569473 / 500000000000000)) * ((37707618859 / 1000000000000000000))) + ((917956049 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12873) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((457591543 / 100000000000000000000) : ℝ) + ((917956049 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12873

namespace BstLean.Part266.Row12873
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12873 164 ∧
    0 ≤ (tableEnvelope C).f1 12873 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12873 164 ∧
    0 ≤ (tableEnvelope C).w1 12873 164 ∧ 0 ≤ (tableEnvelope C).w2 12873 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12873 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12873 164 ∧ 0 ≤ d.f1 12873 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12873 164 ∧ 0 ≤ d.w1 12873 164 ∧ 0 ≤ d.w2 12873 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12873 ≤ 2 * (228 / 100 : ℝ) / 12873 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12873 ≤ 2 * (370 / 100 : ℝ) / 12873 := by
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
    (completeRAData (tableEnvelope C) 12873 164).locationBound 12873 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12873 164).energyBound 12873 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12873 164) (d.f1 12873 164) d.f2 ≤
      32 * (((4430272839 / 1000000000000000000) : ℝ) + (73900707 / 50000000000000000) + (88810323 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12873 164) (d.w1 12873 164)
      (d.w2 12873 164) ≤
      32 * (((176027503 / 10000000000000000000) : ℝ) + (1252402121 / 100000000000000000000) + (45759599 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12873 164) (d.f1 12873 164) d.f2 ≤
      ((4430272839 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4430272839 / 1000000000000000000)) * ((73900707 / 50000000000000000)) * (126 / 100) +
      2 * (((73900707 / 50000000000000000)) ^ 2 + 2 * ((4430272839 / 1000000000000000000)) * ((88810323 / 250000000000000000))) +
      6 * ((73900707 / 50000000000000000)) * ((88810323 / 250000000000000000)) * (126 / 100) + 8 * ((88810323 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12873 164) (d.f1 12873 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12873 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12873 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12873 164) (d.f1 12873 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12873 164) (d.w1 12873 164) (d.w2 12873 164)
  have hwexpr0 : 0 ≤ d.w0 12873 164 + d.w1 12873 164 * √(π / 2) +
      2 * d.w2 12873 164 + energyR16 12873 *
      radiusPolynomialRoot16 (d.w0 12873 164) (d.w1 12873 164) (d.w2 12873 164) := by
    positivity
  constructor
  · change (12873 : ℝ) ^ 8 * (mA 12873 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12873 164) (d.f1 12873 164) d.f2 + locationR16 12873 *
        radiusPolynomialRoot16 (d.f0 12873 164) (d.f1 12873 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12873 : ℝ) ^ 8 * (mA 12873 : ℝ) ^ 8 *
        ((((4430272839 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4430272839 / 1000000000000000000)) * ((73900707 / 50000000000000000)) * (126 / 100) +
          2 * (((73900707 / 50000000000000000)) ^ 2 + 2 * ((4430272839 / 1000000000000000000)) * ((88810323 / 250000000000000000))) +
          6 * ((73900707 / 50000000000000000)) * ((88810323 / 250000000000000000)) * (126 / 100) + 8 * ((88810323 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12873) *
          (32 * (((4430272839 / 1000000000000000000) : ℝ) + (73900707 / 50000000000000000) + (88810323 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12873 : ℝ) ^ 16 *
      (d.w0 12873 164 + d.w1 12873 164 * √(π / 2) + 2 * d.w2 12873 164 +
        energyR16 12873 * radiusPolynomialRoot16 (d.w0 12873 164) (d.w1 12873 164)
          (d.w2 12873 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12873 : ℝ) ^ 16 *
        (((176027503 / 10000000000000000000) : ℝ) + ((1252402121 / 100000000000000000000)) * (126 / 100) + 2 * ((45759599 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12873) *
          (32 * (((176027503 / 10000000000000000000) : ℝ) + (1252402121 / 100000000000000000000) + (45759599 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12873

/-! A coarse bound on the actual paper statistics constant at dimension 12874. -/
namespace BstLean.Part266.Row12874
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12872 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12872 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12872 128 ≤ (13126 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13126 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12874) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12874 : ℕ))
    (by norm_num : (12874 : ℕ) ≤ 16384)
  have ht : paperTail256 12874 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12874 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12874 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12874 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12874 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12874 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12872 128 * √(2 / (12874 : ℝ)) *
      (√(12874 : ℝ) + paperT0 12874 + paperTail256 12874) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12874 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12874 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12874 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12872 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12872 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12874 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12874

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12874
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12874 (61 / 100) 164 (17 / (100 * 12874)) (26 / (10 * 12874)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12874 (61 / 100) 164 (17 / (100 * 12874)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (228742457 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (177677847 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4586901543 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12874 / 12874 * (61 / 100)) ^ 4 * inverseRadius8 (12874 - 1) /
            envelopeGap 12874 (61 / 100) 164 (17 / (100 * 12874)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12874

namespace BstLean.Part266.Row12874
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12874 164 ≤ (4429415549 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12874 164 ≤ (1477727823 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (355172391 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12874 164 ≤ (219983183 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12874 164 ≤ (62605529 / 5000000000000000000)
  w2 : (tableEnvelope C).w2 12874 164 ≤ (228744679 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (228742457 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (228742457 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (177677847 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4586901543 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((726771 / 200000000) : ℝ) ≤ √(17 / (100 * 12874) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12874) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1069444849 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18850880457 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12874) * 164 ≤ 186 / 10000 := by
    have hs : √(tA 12874) ≤ (109850363 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12874) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12874 * (164 : ℝ) ^ 2 + 26 / (10 * 12874) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12874) : ℝ)) (tA 12874 * 164 ^ 2 + 26 / (10 * 12874)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((726771 / 200000000))) * ((228742457 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((726771 / 200000000)) ^ 3) * ((177677847 / 125000000000000000000000))) + ((4586901543 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((726771 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12874) : ℝ)) d.D d.V d.P (√(tA 12874) * 164) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((726771 / 200000000)) ^ 2 * (((1069444849 / 500000000000000)) * ((18850880457 / 500000000000000000)))) + ((4586901543 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12874) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((726771 / 200000000)) * ((228742457 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12874) : ℝ)) (tA 12874 * 164 ^ 2 + 26 / (10 * 12874)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((228742457 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((726771 / 200000000)) ^ 2) * ((177677847 / 125000000000000000000000)) + ((4586901543 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12874) : ℝ)) (√(26 / (10 * 12874) : ℝ)) d.D d.V d.P (√(tA 12874) * 164) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((726771 / 200000000)) * (((1069444849 / 500000000000000)) * ((18850880457 / 500000000000000000))) + ((4586901543 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12874) * 164) ≤ _
    unfold AW2
    calc
      _ ≤ ((228742457 / 50000000000000000000) : ℝ) + ((4586901543 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12874

namespace BstLean.Part266.Row12874
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12874 164 ∧
    0 ≤ (tableEnvelope C).f1 12874 164 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12874 164 ∧
    0 ≤ (tableEnvelope C).w1 12874 164 ∧ 0 ≤ (tableEnvelope C).w2 12874 164 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12874 * (164 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12874 164 ∧ 0 ≤ d.f1 12874 164 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12874 164 ∧ 0 ≤ d.w1 12874 164 ∧ 0 ≤ d.w2 12874 164
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12874 ≤ 2 * (228 / 100 : ℝ) / 12874 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12874 ≤ 2 * (370 / 100 : ℝ) / 12874 := by
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
    (completeRAData (tableEnvelope C) 12874 164).locationBound 12874 164 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12874 164).energyBound 12874 164 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12874 164) (d.f1 12874 164) d.f2 ≤
      32 * (((4429415549 / 1000000000000000000) : ℝ) + (1477727823 / 1000000000000000000) + (355172391 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12874 164) (d.w1 12874 164)
      (d.w2 12874 164) ≤
      32 * (((219983183 / 12500000000000000000) : ℝ) + (62605529 / 5000000000000000000) + (228744679 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12874 164) (d.f1 12874 164) d.f2 ≤
      ((4429415549 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4429415549 / 1000000000000000000)) * ((1477727823 / 1000000000000000000)) * (126 / 100) +
      2 * (((1477727823 / 1000000000000000000)) ^ 2 + 2 * ((4429415549 / 1000000000000000000)) * ((355172391 / 1000000000000000000))) +
      6 * ((1477727823 / 1000000000000000000)) * ((355172391 / 1000000000000000000)) * (126 / 100) + 8 * ((355172391 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12874 164) (d.f1 12874 164) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12874 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12874 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12874 164) (d.f1 12874 164) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12874 164) (d.w1 12874 164) (d.w2 12874 164)
  have hwexpr0 : 0 ≤ d.w0 12874 164 + d.w1 12874 164 * √(π / 2) +
      2 * d.w2 12874 164 + energyR16 12874 *
      radiusPolynomialRoot16 (d.w0 12874 164) (d.w1 12874 164) (d.w2 12874 164) := by
    positivity
  constructor
  · change (12874 : ℝ) ^ 8 * (mA 12874 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12874 164) (d.f1 12874 164) d.f2 + locationR16 12874 *
        radiusPolynomialRoot16 (d.f0 12874 164) (d.f1 12874 164) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12874 : ℝ) ^ 8 * (mA 12874 : ℝ) ^ 8 *
        ((((4429415549 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4429415549 / 1000000000000000000)) * ((1477727823 / 1000000000000000000)) * (126 / 100) +
          2 * (((1477727823 / 1000000000000000000)) ^ 2 + 2 * ((4429415549 / 1000000000000000000)) * ((355172391 / 1000000000000000000))) +
          6 * ((1477727823 / 1000000000000000000)) * ((355172391 / 1000000000000000000)) * (126 / 100) + 8 * ((355172391 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12874) *
          (32 * (((4429415549 / 1000000000000000000) : ℝ) + (1477727823 / 1000000000000000000) + (355172391 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12874 : ℝ) ^ 16 *
      (d.w0 12874 164 + d.w1 12874 164 * √(π / 2) + 2 * d.w2 12874 164 +
        energyR16 12874 * radiusPolynomialRoot16 (d.w0 12874 164) (d.w1 12874 164)
          (d.w2 12874 164)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12874 : ℝ) ^ 16 *
        (((219983183 / 12500000000000000000) : ℝ) + ((62605529 / 5000000000000000000)) * (126 / 100) + 2 * ((228744679 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12874) *
          (32 * (((219983183 / 12500000000000000000) : ℝ) + (62605529 / 5000000000000000000) + (228744679 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12874
