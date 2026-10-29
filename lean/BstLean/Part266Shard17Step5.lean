import BstLean.Part266Shard17Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12775. -/
namespace BstLean.Part266.Row12775
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12773 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12773 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12773 128 ≤ (13027 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13027 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12775) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12775 : ℕ))
    (by norm_num : (12775 : ℕ) ≤ 16384)
  have ht : paperTail256 12775 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12775 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12775 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12775 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12775 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12775 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12773 128 * √(2 / (12775 : ℝ)) *
      (√(12775 : ℝ) + paperT0 12775 + paperTail256 12775) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12775 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12775 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12775 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12773 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12773 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12775 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12775

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12775
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12775 (61 / 100) 163 (17 / (100 * 12775)) (26 / (10 * 12775)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12775 (61 / 100) 163 (17 / (100 * 12775)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (234101983 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (733000349 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (487976289 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12775 / 12775 * (61 / 100)) ^ 4 * inverseRadius8 (12775 - 1) /
            envelopeGap 12775 (61 / 100) 163 (17 / (100 * 12775)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12775

namespace BstLean.Part266.Row12775
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12775 163 ≤ (2257865899 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12775 163 ≤ (1506524717 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (45261727 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12775 163 ≤ (180109921 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12775 163 ≤ (1281447747 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12775 163 ≤ (468208693 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (234101983 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (234101983 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (733000349 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (487976289 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3647909 / 1000000000) : ℝ) ≤ √(17 / (100 * 12775) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12775) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2163802131 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19144194277 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12775) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12775) ≤ (110701649 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12775) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12775 * (163 : ℝ) ^ 2 + 26 / (10 * 12775) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12775) : ℝ)) (tA 12775 * 163 ^ 2 + 26 / (10 * 12775)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3647909 / 1000000000))) * ((234101983 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3647909 / 1000000000)) ^ 3) * ((733000349 / 500000000000000000000000))) + ((487976289 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3647909 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12775) : ℝ)) d.D d.V d.P (√(tA 12775) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3647909 / 1000000000)) ^ 2 * (((2163802131 / 1000000000000000)) * ((19144194277 / 500000000000000000)))) + ((487976289 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12775) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3647909 / 1000000000)) * ((234101983 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12775) : ℝ)) (tA 12775 * 163 ^ 2 + 26 / (10 * 12775)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((234101983 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3647909 / 1000000000)) ^ 2) * ((733000349 / 500000000000000000000000)) + ((487976289 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12775) : ℝ)) (√(26 / (10 * 12775) : ℝ)) d.D d.V d.P (√(tA 12775) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3647909 / 1000000000)) * (((2163802131 / 1000000000000000)) * ((19144194277 / 500000000000000000))) + ((487976289 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12775) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((234101983 / 50000000000000000000) : ℝ) + ((487976289 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12775

namespace BstLean.Part266.Row12775
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12775 163 ∧
    0 ≤ (tableEnvelope C).f1 12775 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12775 163 ∧
    0 ≤ (tableEnvelope C).w1 12775 163 ∧ 0 ≤ (tableEnvelope C).w2 12775 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12775 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12775 163 ∧ 0 ≤ d.f1 12775 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12775 163 ∧ 0 ≤ d.w1 12775 163 ∧ 0 ≤ d.w2 12775 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12775 ≤ 2 * (228 / 100 : ℝ) / 12775 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12775 ≤ 2 * (370 / 100 : ℝ) / 12775 := by
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
    (completeRAData (tableEnvelope C) 12775 163).locationBound 12775 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12775 163).energyBound 12775 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12775 163) (d.f1 12775 163) d.f2 ≤
      32 * (((2257865899 / 500000000000000000) : ℝ) + (1506524717 / 1000000000000000000) + (45261727 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12775 163) (d.w1 12775 163)
      (d.w2 12775 163) ≤
      32 * (((180109921 / 10000000000000000000) : ℝ) + (1281447747 / 100000000000000000000) + (468208693 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12775 163) (d.f1 12775 163) d.f2 ≤
      ((2257865899 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2257865899 / 500000000000000000)) * ((1506524717 / 1000000000000000000)) * (126 / 100) +
      2 * (((1506524717 / 1000000000000000000)) ^ 2 + 2 * ((2257865899 / 500000000000000000)) * ((45261727 / 125000000000000000))) +
      6 * ((1506524717 / 1000000000000000000)) * ((45261727 / 125000000000000000)) * (126 / 100) + 8 * ((45261727 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12775 163) (d.f1 12775 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12775 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12775 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12775 163) (d.f1 12775 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12775 163) (d.w1 12775 163) (d.w2 12775 163)
  have hwexpr0 : 0 ≤ d.w0 12775 163 + d.w1 12775 163 * √(π / 2) +
      2 * d.w2 12775 163 + energyR16 12775 *
      radiusPolynomialRoot16 (d.w0 12775 163) (d.w1 12775 163) (d.w2 12775 163) := by
    positivity
  constructor
  · change (12775 : ℝ) ^ 8 * (mA 12775 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12775 163) (d.f1 12775 163) d.f2 + locationR16 12775 *
        radiusPolynomialRoot16 (d.f0 12775 163) (d.f1 12775 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12775 : ℝ) ^ 8 * (mA 12775 : ℝ) ^ 8 *
        ((((2257865899 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2257865899 / 500000000000000000)) * ((1506524717 / 1000000000000000000)) * (126 / 100) +
          2 * (((1506524717 / 1000000000000000000)) ^ 2 + 2 * ((2257865899 / 500000000000000000)) * ((45261727 / 125000000000000000))) +
          6 * ((1506524717 / 1000000000000000000)) * ((45261727 / 125000000000000000)) * (126 / 100) + 8 * ((45261727 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12775) *
          (32 * (((2257865899 / 500000000000000000) : ℝ) + (1506524717 / 1000000000000000000) + (45261727 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12775 : ℝ) ^ 16 *
      (d.w0 12775 163 + d.w1 12775 163 * √(π / 2) + 2 * d.w2 12775 163 +
        energyR16 12775 * radiusPolynomialRoot16 (d.w0 12775 163) (d.w1 12775 163)
          (d.w2 12775 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12775 : ℝ) ^ 16 *
        (((180109921 / 10000000000000000000) : ℝ) + ((1281447747 / 100000000000000000000)) * (126 / 100) + 2 * ((468208693 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12775) *
          (32 * (((180109921 / 10000000000000000000) : ℝ) + (1281447747 / 100000000000000000000) + (468208693 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12775

/-! A coarse bound on the actual paper statistics constant at dimension 12776. -/
namespace BstLean.Part266.Row12776
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12774 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12774 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12774 128 ≤ (13028 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13028 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12776) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12776 : ℕ))
    (by norm_num : (12776 : ℕ) ≤ 16384)
  have ht : paperTail256 12776 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12776 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12776 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12776 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12776 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12776 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12774 128 * √(2 / (12776 : ℝ)) *
      (√(12776 : ℝ) + paperT0 12776 + paperTail256 12776) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12776 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12776 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12776 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12774 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12774 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12776 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12776

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12776
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12776 (61 / 100) 163 (17 / (100 * 12776)) (26 / (10 * 12776)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12776 (61 / 100) 163 (17 / (100 * 12776)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (117023507 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (366385437 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4876678747 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12776 / 12776 * (61 / 100)) ^ 4 * inverseRadius8 (12776 - 1) /
            envelopeGap 12776 (61 / 100) 163 (17 / (100 * 12776)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12776

namespace BstLean.Part266.Row12776
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12776 163 ≤ (4514848991 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12776 163 ≤ (1506230113 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (72404597 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12776 163 ≤ (360135293 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12776 163 ≤ (1281146933 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12776 163 ≤ (7314043 / 1562500000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (117023507 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (117023507 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (366385437 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4876678747 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1823883 / 500000000) : ℝ) ≤ √(17 / (100 * 12776) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12776) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2163548077 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38282394753 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12776) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12776) ≤ (13836623 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12776) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12776 * (163 : ℝ) ^ 2 + 26 / (10 * 12776) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12776) : ℝ)) (tA 12776 * 163 ^ 2 + 26 / (10 * 12776)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1823883 / 500000000))) * ((117023507 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1823883 / 500000000)) ^ 3) * ((366385437 / 250000000000000000000000))) + ((4876678747 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1823883 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12776) : ℝ)) d.D d.V d.P (√(tA 12776) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1823883 / 500000000)) ^ 2 * (((2163548077 / 1000000000000000)) * ((38282394753 / 1000000000000000000)))) + ((4876678747 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12776) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1823883 / 500000000)) * ((117023507 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12776) : ℝ)) (tA 12776 * 163 ^ 2 + 26 / (10 * 12776)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((117023507 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1823883 / 500000000)) ^ 2) * ((366385437 / 250000000000000000000000)) + ((4876678747 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12776) : ℝ)) (√(26 / (10 * 12776) : ℝ)) d.D d.V d.P (√(tA 12776) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1823883 / 500000000)) * (((2163548077 / 1000000000000000)) * ((38282394753 / 1000000000000000000))) + ((4876678747 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12776) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((117023507 / 25000000000000000000) : ℝ) + ((4876678747 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12776

namespace BstLean.Part266.Row12776
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12776 163 ∧
    0 ≤ (tableEnvelope C).f1 12776 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12776 163 ∧
    0 ≤ (tableEnvelope C).w1 12776 163 ∧ 0 ≤ (tableEnvelope C).w2 12776 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12776 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12776 163 ∧ 0 ≤ d.f1 12776 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12776 163 ∧ 0 ≤ d.w1 12776 163 ∧ 0 ≤ d.w2 12776 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12776 ≤ 2 * (228 / 100 : ℝ) / 12776 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12776 ≤ 2 * (370 / 100 : ℝ) / 12776 := by
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
    (completeRAData (tableEnvelope C) 12776 163).locationBound 12776 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12776 163).energyBound 12776 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12776 163) (d.f1 12776 163) d.f2 ≤
      32 * (((4514848991 / 1000000000000000000) : ℝ) + (1506230113 / 1000000000000000000) + (72404597 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12776 163) (d.w1 12776 163)
      (d.w2 12776 163) ≤
      32 * (((360135293 / 20000000000000000000) : ℝ) + (1281146933 / 100000000000000000000) + (7314043 / 1562500000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12776 163) (d.f1 12776 163) d.f2 ≤
      ((4514848991 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4514848991 / 1000000000000000000)) * ((1506230113 / 1000000000000000000)) * (126 / 100) +
      2 * (((1506230113 / 1000000000000000000)) ^ 2 + 2 * ((4514848991 / 1000000000000000000)) * ((72404597 / 200000000000000000))) +
      6 * ((1506230113 / 1000000000000000000)) * ((72404597 / 200000000000000000)) * (126 / 100) + 8 * ((72404597 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12776 163) (d.f1 12776 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12776 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12776 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12776 163) (d.f1 12776 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12776 163) (d.w1 12776 163) (d.w2 12776 163)
  have hwexpr0 : 0 ≤ d.w0 12776 163 + d.w1 12776 163 * √(π / 2) +
      2 * d.w2 12776 163 + energyR16 12776 *
      radiusPolynomialRoot16 (d.w0 12776 163) (d.w1 12776 163) (d.w2 12776 163) := by
    positivity
  constructor
  · change (12776 : ℝ) ^ 8 * (mA 12776 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12776 163) (d.f1 12776 163) d.f2 + locationR16 12776 *
        radiusPolynomialRoot16 (d.f0 12776 163) (d.f1 12776 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12776 : ℝ) ^ 8 * (mA 12776 : ℝ) ^ 8 *
        ((((4514848991 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4514848991 / 1000000000000000000)) * ((1506230113 / 1000000000000000000)) * (126 / 100) +
          2 * (((1506230113 / 1000000000000000000)) ^ 2 + 2 * ((4514848991 / 1000000000000000000)) * ((72404597 / 200000000000000000))) +
          6 * ((1506230113 / 1000000000000000000)) * ((72404597 / 200000000000000000)) * (126 / 100) + 8 * ((72404597 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12776) *
          (32 * (((4514848991 / 1000000000000000000) : ℝ) + (1506230113 / 1000000000000000000) + (72404597 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12776 : ℝ) ^ 16 *
      (d.w0 12776 163 + d.w1 12776 163 * √(π / 2) + 2 * d.w2 12776 163 +
        energyR16 12776 * radiusPolynomialRoot16 (d.w0 12776 163) (d.w1 12776 163)
          (d.w2 12776 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12776 : ℝ) ^ 16 *
        (((360135293 / 20000000000000000000) : ℝ) + ((1281146933 / 100000000000000000000)) * (126 / 100) + 2 * ((7314043 / 1562500000000000000)) +
          (2 * (370 / 100 : ℝ) / 12776) *
          (32 * (((360135293 / 20000000000000000000) : ℝ) + (1281146933 / 100000000000000000000) + (7314043 / 1562500000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12776

/-! A coarse bound on the actual paper statistics constant at dimension 12777. -/
namespace BstLean.Part266.Row12777
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12775 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12775 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12775 128 ≤ (13029 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13029 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12777) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12777 : ℕ))
    (by norm_num : (12777 : ℕ) ≤ 16384)
  have ht : paperTail256 12777 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12777 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12777 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12777 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12777 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12777 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12775 128 * √(2 / (12777 : ℝ)) *
      (√(12777 : ℝ) + paperT0 12777 + paperTail256 12777) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12777 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12777 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12777 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12775 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12775 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12777 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12777

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12777
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12777 (61 / 100) 163 (17 / (100 * 12777)) (26 / (10 * 12777)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12777 (61 / 100) 163 (17 / (100 * 12777)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (467984123 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (732541489 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1522999 / 312500000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12777 / 12777 * (61 / 100)) ^ 4 * inverseRadius8 (12777 - 1) /
            envelopeGap 12777 (61 / 100) 163 (17 / (100 * 12777)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12777

namespace BstLean.Part266.Row12777
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12777 163 ≤ (2256983243 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12777 163 ≤ (752967801 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (180976087 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12777 163 ≤ (360050773 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12777 163 ≤ (640423109 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12777 163 ≤ (116997211 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (467984123 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (467984123 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (732541489 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1522999 / 312500000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3647623 / 1000000000) : ℝ) ≤ √(17 / (100 * 12777) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12777) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (216329407 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7655280473 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12777) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12777) ≤ (110684321 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12777) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12777 * (163 : ℝ) ^ 2 + 26 / (10 * 12777) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12777) : ℝ)) (tA 12777 * 163 ^ 2 + 26 / (10 * 12777)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3647623 / 1000000000))) * ((467984123 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3647623 / 1000000000)) ^ 3) * ((732541489 / 500000000000000000000000))) + ((1522999 / 312500000000000000000)) * (3 / 2 * (39895 / 100000) / ((3647623 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12777) : ℝ)) d.D d.V d.P (√(tA 12777) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3647623 / 1000000000)) ^ 2 * (((216329407 / 100000000000000)) * ((7655280473 / 200000000000000000)))) + ((1522999 / 312500000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12777) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3647623 / 1000000000)) * ((467984123 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12777) : ℝ)) (tA 12777 * 163 ^ 2 + 26 / (10 * 12777)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((467984123 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3647623 / 1000000000)) ^ 2) * ((732541489 / 500000000000000000000000)) + ((1522999 / 312500000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12777) : ℝ)) (√(26 / (10 * 12777) : ℝ)) d.D d.V d.P (√(tA 12777) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3647623 / 1000000000)) * (((216329407 / 100000000000000)) * ((7655280473 / 200000000000000000))) + ((1522999 / 312500000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12777) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((467984123 / 100000000000000000000) : ℝ) + ((1522999 / 312500000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12777

namespace BstLean.Part266.Row12777
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12777 163 ∧
    0 ≤ (tableEnvelope C).f1 12777 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12777 163 ∧
    0 ≤ (tableEnvelope C).w1 12777 163 ∧ 0 ≤ (tableEnvelope C).w2 12777 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12777 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12777 163 ∧ 0 ≤ d.f1 12777 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12777 163 ∧ 0 ≤ d.w1 12777 163 ∧ 0 ≤ d.w2 12777 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12777 ≤ 2 * (228 / 100 : ℝ) / 12777 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12777 ≤ 2 * (370 / 100 : ℝ) / 12777 := by
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
    (completeRAData (tableEnvelope C) 12777 163).locationBound 12777 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12777 163).energyBound 12777 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12777 163) (d.f1 12777 163) d.f2 ≤
      32 * (((2256983243 / 500000000000000000) : ℝ) + (752967801 / 500000000000000000) + (180976087 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12777 163) (d.w1 12777 163)
      (d.w2 12777 163) ≤
      32 * (((360050773 / 20000000000000000000) : ℝ) + (640423109 / 50000000000000000000) + (116997211 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12777 163) (d.f1 12777 163) d.f2 ≤
      ((2256983243 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2256983243 / 500000000000000000)) * ((752967801 / 500000000000000000)) * (126 / 100) +
      2 * (((752967801 / 500000000000000000)) ^ 2 + 2 * ((2256983243 / 500000000000000000)) * ((180976087 / 500000000000000000))) +
      6 * ((752967801 / 500000000000000000)) * ((180976087 / 500000000000000000)) * (126 / 100) + 8 * ((180976087 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12777 163) (d.f1 12777 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12777 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12777 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12777 163) (d.f1 12777 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12777 163) (d.w1 12777 163) (d.w2 12777 163)
  have hwexpr0 : 0 ≤ d.w0 12777 163 + d.w1 12777 163 * √(π / 2) +
      2 * d.w2 12777 163 + energyR16 12777 *
      radiusPolynomialRoot16 (d.w0 12777 163) (d.w1 12777 163) (d.w2 12777 163) := by
    positivity
  constructor
  · change (12777 : ℝ) ^ 8 * (mA 12777 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12777 163) (d.f1 12777 163) d.f2 + locationR16 12777 *
        radiusPolynomialRoot16 (d.f0 12777 163) (d.f1 12777 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12777 : ℝ) ^ 8 * (mA 12777 : ℝ) ^ 8 *
        ((((2256983243 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2256983243 / 500000000000000000)) * ((752967801 / 500000000000000000)) * (126 / 100) +
          2 * (((752967801 / 500000000000000000)) ^ 2 + 2 * ((2256983243 / 500000000000000000)) * ((180976087 / 500000000000000000))) +
          6 * ((752967801 / 500000000000000000)) * ((180976087 / 500000000000000000)) * (126 / 100) + 8 * ((180976087 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12777) *
          (32 * (((2256983243 / 500000000000000000) : ℝ) + (752967801 / 500000000000000000) + (180976087 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12777 : ℝ) ^ 16 *
      (d.w0 12777 163 + d.w1 12777 163 * √(π / 2) + 2 * d.w2 12777 163 +
        energyR16 12777 * radiusPolynomialRoot16 (d.w0 12777 163) (d.w1 12777 163)
          (d.w2 12777 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12777 : ℝ) ^ 16 *
        (((360050773 / 20000000000000000000) : ℝ) + ((640423109 / 50000000000000000000)) * (126 / 100) + 2 * ((116997211 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12777) *
          (32 * (((360050773 / 20000000000000000000) : ℝ) + (640423109 / 50000000000000000000) + (116997211 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12777

/-! A coarse bound on the actual paper statistics constant at dimension 12778. -/
namespace BstLean.Part266.Row12778
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12776 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12776 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12776 128 ≤ (13030 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13030 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12778) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12778 : ℕ))
    (by norm_num : (12778 : ℕ) ≤ 16384)
  have ht : paperTail256 12778 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12778 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12778 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12778 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12778 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12778 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12776 128 * √(2 / (12778 : ℝ)) *
      (√(12778 : ℝ) + paperT0 12778 + paperTail256 12778) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12778 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12778 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12778 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12776 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12776 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12778 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12778

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12778
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12778 (61 / 100) 163 (17 / (100 * 12778)) (26 / (10 * 12778)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12778 (61 / 100) 163 (17 / (100 * 12778)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (233937127 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1464624387 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (974103409 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12778 / 12778 * (61 / 100)) ^ 4 * inverseRadius8 (12778 - 1) /
            envelopeGap 12778 (61 / 100) 163 (17 / (100 * 12778)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12778

namespace BstLean.Part266.Row12778
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12778 163 ≤ (4513084283 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12778 163 ≤ (1505641187 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (72376277 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12778 163 ≤ (179983141 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12778 163 ≤ (256109121 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12778 163 ≤ (467878973 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (233937127 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (233937127 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1464624387 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (974103409 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((91187 / 25000000) : ℝ) ≤ √(17 / (100 * 12778) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12778) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (540760029 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19135205689 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12778) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12778) ≤ (110675659 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12778) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12778 * (163 : ℝ) ^ 2 + 26 / (10 * 12778) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12778) : ℝ)) (tA 12778 * 163 ^ 2 + 26 / (10 * 12778)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((91187 / 25000000))) * ((233937127 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((91187 / 25000000)) ^ 3) * ((1464624387 / 1000000000000000000000000))) + ((974103409 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((91187 / 25000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12778) : ℝ)) d.D d.V d.P (√(tA 12778) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((91187 / 25000000)) ^ 2 * (((540760029 / 250000000000000)) * ((19135205689 / 500000000000000000)))) + ((974103409 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12778) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((91187 / 25000000)) * ((233937127 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12778) : ℝ)) (tA 12778 * 163 ^ 2 + 26 / (10 * 12778)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((233937127 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((91187 / 25000000)) ^ 2) * ((1464624387 / 1000000000000000000000000)) + ((974103409 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12778) : ℝ)) (√(26 / (10 * 12778) : ℝ)) d.D d.V d.P (√(tA 12778) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((91187 / 25000000)) * (((540760029 / 250000000000000)) * ((19135205689 / 500000000000000000))) + ((974103409 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12778) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((233937127 / 50000000000000000000) : ℝ) + ((974103409 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12778

namespace BstLean.Part266.Row12778
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12778 163 ∧
    0 ≤ (tableEnvelope C).f1 12778 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12778 163 ∧
    0 ≤ (tableEnvelope C).w1 12778 163 ∧ 0 ≤ (tableEnvelope C).w2 12778 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12778 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12778 163 ∧ 0 ≤ d.f1 12778 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12778 163 ∧ 0 ≤ d.w1 12778 163 ∧ 0 ≤ d.w2 12778 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12778 ≤ 2 * (228 / 100 : ℝ) / 12778 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12778 ≤ 2 * (370 / 100 : ℝ) / 12778 := by
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
    (completeRAData (tableEnvelope C) 12778 163).locationBound 12778 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12778 163).energyBound 12778 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12778 163) (d.f1 12778 163) d.f2 ≤
      32 * (((4513084283 / 1000000000000000000) : ℝ) + (1505641187 / 1000000000000000000) + (72376277 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12778 163) (d.w1 12778 163)
      (d.w2 12778 163) ≤
      32 * (((179983141 / 10000000000000000000) : ℝ) + (256109121 / 20000000000000000000) + (467878973 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12778 163) (d.f1 12778 163) d.f2 ≤
      ((4513084283 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4513084283 / 1000000000000000000)) * ((1505641187 / 1000000000000000000)) * (126 / 100) +
      2 * (((1505641187 / 1000000000000000000)) ^ 2 + 2 * ((4513084283 / 1000000000000000000)) * ((72376277 / 200000000000000000))) +
      6 * ((1505641187 / 1000000000000000000)) * ((72376277 / 200000000000000000)) * (126 / 100) + 8 * ((72376277 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12778 163) (d.f1 12778 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12778 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12778 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12778 163) (d.f1 12778 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12778 163) (d.w1 12778 163) (d.w2 12778 163)
  have hwexpr0 : 0 ≤ d.w0 12778 163 + d.w1 12778 163 * √(π / 2) +
      2 * d.w2 12778 163 + energyR16 12778 *
      radiusPolynomialRoot16 (d.w0 12778 163) (d.w1 12778 163) (d.w2 12778 163) := by
    positivity
  constructor
  · change (12778 : ℝ) ^ 8 * (mA 12778 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12778 163) (d.f1 12778 163) d.f2 + locationR16 12778 *
        radiusPolynomialRoot16 (d.f0 12778 163) (d.f1 12778 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12778 : ℝ) ^ 8 * (mA 12778 : ℝ) ^ 8 *
        ((((4513084283 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4513084283 / 1000000000000000000)) * ((1505641187 / 1000000000000000000)) * (126 / 100) +
          2 * (((1505641187 / 1000000000000000000)) ^ 2 + 2 * ((4513084283 / 1000000000000000000)) * ((72376277 / 200000000000000000))) +
          6 * ((1505641187 / 1000000000000000000)) * ((72376277 / 200000000000000000)) * (126 / 100) + 8 * ((72376277 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12778) *
          (32 * (((4513084283 / 1000000000000000000) : ℝ) + (1505641187 / 1000000000000000000) + (72376277 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12778 : ℝ) ^ 16 *
      (d.w0 12778 163 + d.w1 12778 163 * √(π / 2) + 2 * d.w2 12778 163 +
        energyR16 12778 * radiusPolynomialRoot16 (d.w0 12778 163) (d.w1 12778 163)
          (d.w2 12778 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12778 : ℝ) ^ 16 *
        (((179983141 / 10000000000000000000) : ℝ) + ((256109121 / 20000000000000000000)) * (126 / 100) + 2 * ((467878973 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12778) *
          (32 * (((179983141 / 10000000000000000000) : ℝ) + (256109121 / 20000000000000000000) + (467878973 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12778

/-! A coarse bound on the actual paper statistics constant at dimension 12779. -/
namespace BstLean.Part266.Row12779
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12777 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12777 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12777 128 ≤ (13031 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13031 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12779) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12779 : ℕ))
    (by norm_num : (12779 : ℕ) ≤ 16384)
  have ht : paperTail256 12779 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12779 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12779 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12779 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12779 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12779 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12777 128 * √(2 / (12779 : ℝ)) *
      (√(12779 : ℝ) + paperT0 12779 + paperTail256 12779) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12779 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12779 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12779 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12777 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12777 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12779 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12779

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12779
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12779 (61 / 100) 163 (17 / (100 * 12779)) (26 / (10 * 12779)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12779 (61 / 100) 163 (17 / (100 * 12779)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (233882209 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (58566639 / 40000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4867439483 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12779 / 12779 * (61 / 100)) ^ 4 * inverseRadius8 (12779 - 1) /
            envelopeGap 12779 (61 / 100) 163 (17 / (100 * 12779)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12779

namespace BstLean.Part266.Row12779
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12779 163 ≤ (564024851 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12779 163 ≤ (1505346039 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (361810517 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12779 163 ≤ (1799408367 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12779 163 ≤ (1280244739 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12779 163 ≤ (233884567 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (233882209 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (233882209 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (58566639 / 40000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4867439483 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1823669 / 500000000) : ℝ) ≤ √(17 / (100 * 12779) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12779) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (67587069 / 31250000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1195763181 / 31250000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12779) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12779) ≤ (55333499 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12779) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12779 * (163 : ℝ) ^ 2 + 26 / (10 * 12779) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12779) : ℝ)) (tA 12779 * 163 ^ 2 + 26 / (10 * 12779)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1823669 / 500000000))) * ((233882209 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1823669 / 500000000)) ^ 3) * ((58566639 / 40000000000000000000000))) + ((4867439483 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1823669 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12779) : ℝ)) d.D d.V d.P (√(tA 12779) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1823669 / 500000000)) ^ 2 * (((67587069 / 31250000000000)) * ((1195763181 / 31250000000000000)))) + ((4867439483 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12779) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1823669 / 500000000)) * ((233882209 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12779) : ℝ)) (tA 12779 * 163 ^ 2 + 26 / (10 * 12779)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((233882209 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1823669 / 500000000)) ^ 2) * ((58566639 / 40000000000000000000000)) + ((4867439483 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12779) : ℝ)) (√(26 / (10 * 12779) : ℝ)) d.D d.V d.P (√(tA 12779) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1823669 / 500000000)) * (((67587069 / 31250000000000)) * ((1195763181 / 31250000000000000))) + ((4867439483 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12779) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((233882209 / 50000000000000000000) : ℝ) + ((4867439483 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12779

namespace BstLean.Part266.Row12779
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12779 163 ∧
    0 ≤ (tableEnvelope C).f1 12779 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12779 163 ∧
    0 ≤ (tableEnvelope C).w1 12779 163 ∧ 0 ≤ (tableEnvelope C).w2 12779 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12779 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12779 163 ∧ 0 ≤ d.f1 12779 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12779 163 ∧ 0 ≤ d.w1 12779 163 ∧ 0 ≤ d.w2 12779 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12779 ≤ 2 * (228 / 100 : ℝ) / 12779 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12779 ≤ 2 * (370 / 100 : ℝ) / 12779 := by
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
    (completeRAData (tableEnvelope C) 12779 163).locationBound 12779 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12779 163).energyBound 12779 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12779 163) (d.f1 12779 163) d.f2 ≤
      32 * (((564024851 / 125000000000000000) : ℝ) + (1505346039 / 1000000000000000000) + (361810517 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12779 163) (d.w1 12779 163)
      (d.w2 12779 163) ≤
      32 * (((1799408367 / 100000000000000000000) : ℝ) + (1280244739 / 100000000000000000000) + (233884567 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12779 163) (d.f1 12779 163) d.f2 ≤
      ((564024851 / 125000000000000000) : ℝ) ^ 2 + 2 * ((564024851 / 125000000000000000)) * ((1505346039 / 1000000000000000000)) * (126 / 100) +
      2 * (((1505346039 / 1000000000000000000)) ^ 2 + 2 * ((564024851 / 125000000000000000)) * ((361810517 / 1000000000000000000))) +
      6 * ((1505346039 / 1000000000000000000)) * ((361810517 / 1000000000000000000)) * (126 / 100) + 8 * ((361810517 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12779 163) (d.f1 12779 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12779 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12779 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12779 163) (d.f1 12779 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12779 163) (d.w1 12779 163) (d.w2 12779 163)
  have hwexpr0 : 0 ≤ d.w0 12779 163 + d.w1 12779 163 * √(π / 2) +
      2 * d.w2 12779 163 + energyR16 12779 *
      radiusPolynomialRoot16 (d.w0 12779 163) (d.w1 12779 163) (d.w2 12779 163) := by
    positivity
  constructor
  · change (12779 : ℝ) ^ 8 * (mA 12779 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12779 163) (d.f1 12779 163) d.f2 + locationR16 12779 *
        radiusPolynomialRoot16 (d.f0 12779 163) (d.f1 12779 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12779 : ℝ) ^ 8 * (mA 12779 : ℝ) ^ 8 *
        ((((564024851 / 125000000000000000) : ℝ) ^ 2 + 2 * ((564024851 / 125000000000000000)) * ((1505346039 / 1000000000000000000)) * (126 / 100) +
          2 * (((1505346039 / 1000000000000000000)) ^ 2 + 2 * ((564024851 / 125000000000000000)) * ((361810517 / 1000000000000000000))) +
          6 * ((1505346039 / 1000000000000000000)) * ((361810517 / 1000000000000000000)) * (126 / 100) + 8 * ((361810517 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12779) *
          (32 * (((564024851 / 125000000000000000) : ℝ) + (1505346039 / 1000000000000000000) + (361810517 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12779 : ℝ) ^ 16 *
      (d.w0 12779 163 + d.w1 12779 163 * √(π / 2) + 2 * d.w2 12779 163 +
        energyR16 12779 * radiusPolynomialRoot16 (d.w0 12779 163) (d.w1 12779 163)
          (d.w2 12779 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12779 : ℝ) ^ 16 *
        (((1799408367 / 100000000000000000000) : ℝ) + ((1280244739 / 100000000000000000000)) * (126 / 100) + 2 * ((233884567 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12779) *
          (32 * (((1799408367 / 100000000000000000000) : ℝ) + (1280244739 / 100000000000000000000) + (233884567 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12779

/-! A coarse bound on the actual paper statistics constant at dimension 12780. -/
namespace BstLean.Part266.Row12780
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12778 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12778 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12778 128 ≤ (13032 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13032 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12780) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12780 : ℕ))
    (by norm_num : (12780 : ℕ) ≤ 16384)
  have ht : paperTail256 12780 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12780 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12780 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12780 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12780 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12780 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12778 128 * √(2 / (12780 : ℝ)) *
      (√(12780 : ℝ) + paperT0 12780 + paperTail256 12780) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12780 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12780 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12780 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12778 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12778 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12780 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12780

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12780
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12780 (61 / 100) 163 (17 / (100 * 12780)) (26 / (10 * 12780)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12780 (61 / 100) 163 (17 / (100 * 12780)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (467654617 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1463707743 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (486436411 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12780 / 12780 * (61 / 100)) ^ 4 * inverseRadius8 (12780 - 1) /
            envelopeGap 12780 (61 / 100) 163 (17 / (100 * 12780)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12780

namespace BstLean.Part266.Row12780
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12780 163 ≤ (563914651 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12780 163 ≤ (376262953 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (36173977 / 100000000000000000)
  w0 : (tableEnvelope C).w0 12780 163 ≤ (8994931 / 500000000000000000)
  w1 : (tableEnvelope C).w1 12780 163 ≤ (51197773 / 4000000000000000000)
  w2 : (tableEnvelope C).w2 12780 163 ≤ (46765933 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (467654617 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (467654617 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1463707743 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (486436411 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((729439 / 200000000) : ℝ) ≤ √(17 / (100 * 12780) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12780) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (263981 / 122070312500) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (1912921681 / 50000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12780) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12780) ≤ (110658339 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12780) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12780 * (163 : ℝ) ^ 2 + 26 / (10 * 12780) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12780) : ℝ)) (tA 12780 * 163 ^ 2 + 26 / (10 * 12780)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((729439 / 200000000))) * ((467654617 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((729439 / 200000000)) ^ 3) * ((1463707743 / 1000000000000000000000000))) + ((486436411 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((729439 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12780) : ℝ)) d.D d.V d.P (√(tA 12780) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((729439 / 200000000)) ^ 2 * (((263981 / 122070312500)) * ((1912921681 / 50000000000000000)))) + ((486436411 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12780) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((729439 / 200000000)) * ((467654617 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12780) : ℝ)) (tA 12780 * 163 ^ 2 + 26 / (10 * 12780)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((467654617 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((729439 / 200000000)) ^ 2) * ((1463707743 / 1000000000000000000000000)) + ((486436411 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12780) : ℝ)) (√(26 / (10 * 12780) : ℝ)) d.D d.V d.P (√(tA 12780) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((729439 / 200000000)) * (((263981 / 122070312500)) * ((1912921681 / 50000000000000000))) + ((486436411 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12780) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((467654617 / 100000000000000000000) : ℝ) + ((486436411 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12780

namespace BstLean.Part266.Row12780
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12780 163 ∧
    0 ≤ (tableEnvelope C).f1 12780 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12780 163 ∧
    0 ≤ (tableEnvelope C).w1 12780 163 ∧ 0 ≤ (tableEnvelope C).w2 12780 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12780 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12780 163 ∧ 0 ≤ d.f1 12780 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12780 163 ∧ 0 ≤ d.w1 12780 163 ∧ 0 ≤ d.w2 12780 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12780 ≤ 2 * (228 / 100 : ℝ) / 12780 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12780 ≤ 2 * (370 / 100 : ℝ) / 12780 := by
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
    (completeRAData (tableEnvelope C) 12780 163).locationBound 12780 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12780 163).energyBound 12780 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12780 163) (d.f1 12780 163) d.f2 ≤
      32 * (((563914651 / 125000000000000000) : ℝ) + (376262953 / 250000000000000000) + (36173977 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12780 163) (d.w1 12780 163)
      (d.w2 12780 163) ≤
      32 * (((8994931 / 500000000000000000) : ℝ) + (51197773 / 4000000000000000000) + (46765933 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12780 163) (d.f1 12780 163) d.f2 ≤
      ((563914651 / 125000000000000000) : ℝ) ^ 2 + 2 * ((563914651 / 125000000000000000)) * ((376262953 / 250000000000000000)) * (126 / 100) +
      2 * (((376262953 / 250000000000000000)) ^ 2 + 2 * ((563914651 / 125000000000000000)) * ((36173977 / 100000000000000000))) +
      6 * ((376262953 / 250000000000000000)) * ((36173977 / 100000000000000000)) * (126 / 100) + 8 * ((36173977 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12780 163) (d.f1 12780 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12780 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12780 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12780 163) (d.f1 12780 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12780 163) (d.w1 12780 163) (d.w2 12780 163)
  have hwexpr0 : 0 ≤ d.w0 12780 163 + d.w1 12780 163 * √(π / 2) +
      2 * d.w2 12780 163 + energyR16 12780 *
      radiusPolynomialRoot16 (d.w0 12780 163) (d.w1 12780 163) (d.w2 12780 163) := by
    positivity
  constructor
  · change (12780 : ℝ) ^ 8 * (mA 12780 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12780 163) (d.f1 12780 163) d.f2 + locationR16 12780 *
        radiusPolynomialRoot16 (d.f0 12780 163) (d.f1 12780 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12780 : ℝ) ^ 8 * (mA 12780 : ℝ) ^ 8 *
        ((((563914651 / 125000000000000000) : ℝ) ^ 2 + 2 * ((563914651 / 125000000000000000)) * ((376262953 / 250000000000000000)) * (126 / 100) +
          2 * (((376262953 / 250000000000000000)) ^ 2 + 2 * ((563914651 / 125000000000000000)) * ((36173977 / 100000000000000000))) +
          6 * ((376262953 / 250000000000000000)) * ((36173977 / 100000000000000000)) * (126 / 100) + 8 * ((36173977 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12780) *
          (32 * (((563914651 / 125000000000000000) : ℝ) + (376262953 / 250000000000000000) + (36173977 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12780 : ℝ) ^ 16 *
      (d.w0 12780 163 + d.w1 12780 163 * √(π / 2) + 2 * d.w2 12780 163 +
        energyR16 12780 * radiusPolynomialRoot16 (d.w0 12780 163) (d.w1 12780 163)
          (d.w2 12780 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12780 : ℝ) ^ 16 *
        (((8994931 / 500000000000000000) : ℝ) + ((51197773 / 4000000000000000000)) * (126 / 100) + 2 * ((46765933 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12780) *
          (32 * (((8994931 / 500000000000000000) : ℝ) + (51197773 / 4000000000000000000) + (46765933 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12780

/-! A coarse bound on the actual paper statistics constant at dimension 12781. -/
namespace BstLean.Part266.Row12781
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12779 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12779 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12779 128 ≤ (13033 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13033 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12781) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12781 : ℕ))
    (by norm_num : (12781 : ℕ) ≤ 16384)
  have ht : paperTail256 12781 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12781 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12781 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12781 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12781 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12781 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12779 128 * √(2 / (12781 : ℝ)) *
      (√(12781 : ℝ) + paperT0 12781 + paperTail256 12781) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12781 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12781 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12781 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12779 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12779 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12781 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12781

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12781
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12781 (61 / 100) 163 (17 / (100 * 12781)) (26 / (10 * 12781)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12781 (61 / 100) 163 (17 / (100 * 12781)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (467544851 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1463249691 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (194451637 / 40000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12781 / 12781 * (61 / 100)) ^ 4 * inverseRadius8 (12781 - 1) /
            envelopeGap 12781 (61 / 100) 163 (17 / (100 * 12781)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12781

namespace BstLean.Part266.Row12781
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12781 163 ≤ (563804489 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12781 163 ≤ (1504757681 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (90417261 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12781 163 ≤ (1798564179 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12781 163 ≤ (319911003 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12781 163 ≤ (467549561 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (467544851 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (467544851 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1463249691 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (194451637 / 40000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((911763 / 250000000) : ℝ) ≤ √(17 / (100 * 12781) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12781) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1081139273 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38252446863 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12781) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12781) ≤ (110649681 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12781) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12781 * (163 : ℝ) ^ 2 + 26 / (10 * 12781) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12781) : ℝ)) (tA 12781 * 163 ^ 2 + 26 / (10 * 12781)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((911763 / 250000000))) * ((467544851 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((911763 / 250000000)) ^ 3) * ((1463249691 / 1000000000000000000000000))) + ((194451637 / 40000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((911763 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12781) : ℝ)) d.D d.V d.P (√(tA 12781) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((911763 / 250000000)) ^ 2 * (((1081139273 / 500000000000000)) * ((38252446863 / 1000000000000000000)))) + ((194451637 / 40000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12781) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((911763 / 250000000)) * ((467544851 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12781) : ℝ)) (tA 12781 * 163 ^ 2 + 26 / (10 * 12781)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((467544851 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((911763 / 250000000)) ^ 2) * ((1463249691 / 1000000000000000000000000)) + ((194451637 / 40000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12781) : ℝ)) (√(26 / (10 * 12781) : ℝ)) d.D d.V d.P (√(tA 12781) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((911763 / 250000000)) * (((1081139273 / 500000000000000)) * ((38252446863 / 1000000000000000000))) + ((194451637 / 40000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12781) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((467544851 / 100000000000000000000) : ℝ) + ((194451637 / 40000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12781

namespace BstLean.Part266.Row12781
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12781 163 ∧
    0 ≤ (tableEnvelope C).f1 12781 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12781 163 ∧
    0 ≤ (tableEnvelope C).w1 12781 163 ∧ 0 ≤ (tableEnvelope C).w2 12781 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12781 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12781 163 ∧ 0 ≤ d.f1 12781 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12781 163 ∧ 0 ≤ d.w1 12781 163 ∧ 0 ≤ d.w2 12781 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12781 ≤ 2 * (228 / 100 : ℝ) / 12781 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12781 ≤ 2 * (370 / 100 : ℝ) / 12781 := by
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
    (completeRAData (tableEnvelope C) 12781 163).locationBound 12781 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12781 163).energyBound 12781 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12781 163) (d.f1 12781 163) d.f2 ≤
      32 * (((563804489 / 125000000000000000) : ℝ) + (1504757681 / 1000000000000000000) + (90417261 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12781 163) (d.w1 12781 163)
      (d.w2 12781 163) ≤
      32 * (((1798564179 / 100000000000000000000) : ℝ) + (319911003 / 25000000000000000000) + (467549561 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12781 163) (d.f1 12781 163) d.f2 ≤
      ((563804489 / 125000000000000000) : ℝ) ^ 2 + 2 * ((563804489 / 125000000000000000)) * ((1504757681 / 1000000000000000000)) * (126 / 100) +
      2 * (((1504757681 / 1000000000000000000)) ^ 2 + 2 * ((563804489 / 125000000000000000)) * ((90417261 / 250000000000000000))) +
      6 * ((1504757681 / 1000000000000000000)) * ((90417261 / 250000000000000000)) * (126 / 100) + 8 * ((90417261 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12781 163) (d.f1 12781 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12781 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12781 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12781 163) (d.f1 12781 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12781 163) (d.w1 12781 163) (d.w2 12781 163)
  have hwexpr0 : 0 ≤ d.w0 12781 163 + d.w1 12781 163 * √(π / 2) +
      2 * d.w2 12781 163 + energyR16 12781 *
      radiusPolynomialRoot16 (d.w0 12781 163) (d.w1 12781 163) (d.w2 12781 163) := by
    positivity
  constructor
  · change (12781 : ℝ) ^ 8 * (mA 12781 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12781 163) (d.f1 12781 163) d.f2 + locationR16 12781 *
        radiusPolynomialRoot16 (d.f0 12781 163) (d.f1 12781 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12781 : ℝ) ^ 8 * (mA 12781 : ℝ) ^ 8 *
        ((((563804489 / 125000000000000000) : ℝ) ^ 2 + 2 * ((563804489 / 125000000000000000)) * ((1504757681 / 1000000000000000000)) * (126 / 100) +
          2 * (((1504757681 / 1000000000000000000)) ^ 2 + 2 * ((563804489 / 125000000000000000)) * ((90417261 / 250000000000000000))) +
          6 * ((1504757681 / 1000000000000000000)) * ((90417261 / 250000000000000000)) * (126 / 100) + 8 * ((90417261 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12781) *
          (32 * (((563804489 / 125000000000000000) : ℝ) + (1504757681 / 1000000000000000000) + (90417261 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12781 : ℝ) ^ 16 *
      (d.w0 12781 163 + d.w1 12781 163 * √(π / 2) + 2 * d.w2 12781 163 +
        energyR16 12781 * radiusPolynomialRoot16 (d.w0 12781 163) (d.w1 12781 163)
          (d.w2 12781 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12781 : ℝ) ^ 16 *
        (((1798564179 / 100000000000000000000) : ℝ) + ((319911003 / 25000000000000000000)) * (126 / 100) + 2 * ((467549561 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12781) *
          (32 * (((1798564179 / 100000000000000000000) : ℝ) + (319911003 / 25000000000000000000) + (467549561 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12781

/-! A coarse bound on the actual paper statistics constant at dimension 12782. -/
namespace BstLean.Part266.Row12782
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12780 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12780 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12780 128 ≤ (13034 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13034 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12782) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12782 : ℕ))
    (by norm_num : (12782 : ℕ) ≤ 16384)
  have ht : paperTail256 12782 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12782 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12782 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12782 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12782 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12782 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12780 128 * √(2 / (12782 : ℝ)) *
      (√(12782 : ℝ) + paperT0 12782 + paperTail256 12782) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12782 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12782 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12782 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12780 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12780 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12782 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12782

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12782
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12782 (61 / 100) 163 (17 / (100 * 12782)) (26 / (10 * 12782)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12782 (61 / 100) 163 (17 / (100 * 12782)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (233717559 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1462791817 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2429109963 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12782 / 12782 * (61 / 100)) ^ 4 * inverseRadius8 (12782 - 1) /
            envelopeGap 12782 (61 / 100) 163 (17 / (100 * 12782)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12782

namespace BstLean.Part266.Row12782
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12782 163 ≤ (4509551343 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12782 163 ≤ (1504462817 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (2259989 / 6250000000000000)
  w0 : (tableEnvelope C).w0 12782 163 ≤ (1798141571 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12782 163 ≤ (639671723 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12782 163 ≤ (18697593 / 4000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (233717559 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (233717559 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1462791817 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2429109963 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((364691 / 100000000) : ℝ) ≤ √(17 / (100 * 12782) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12782) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (540506197 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38246461497 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12782) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12782) ≤ (864383 / 7812500000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12782) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12782 * (163 : ℝ) ^ 2 + 26 / (10 * 12782) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12782) : ℝ)) (tA 12782 * 163 ^ 2 + 26 / (10 * 12782)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((364691 / 100000000))) * ((233717559 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((364691 / 100000000)) ^ 3) * ((1462791817 / 1000000000000000000000000))) + ((2429109963 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((364691 / 100000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12782) : ℝ)) d.D d.V d.P (√(tA 12782) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((364691 / 100000000)) ^ 2 * (((540506197 / 250000000000000)) * ((38246461497 / 1000000000000000000)))) + ((2429109963 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12782) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((364691 / 100000000)) * ((233717559 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12782) : ℝ)) (tA 12782 * 163 ^ 2 + 26 / (10 * 12782)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((233717559 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((364691 / 100000000)) ^ 2) * ((1462791817 / 1000000000000000000000000)) + ((2429109963 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12782) : ℝ)) (√(26 / (10 * 12782) : ℝ)) d.D d.V d.P (√(tA 12782) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((364691 / 100000000)) * (((540506197 / 250000000000000)) * ((38246461497 / 1000000000000000000))) + ((2429109963 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12782) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((233717559 / 50000000000000000000) : ℝ) + ((2429109963 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12782

namespace BstLean.Part266.Row12782
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12782 163 ∧
    0 ≤ (tableEnvelope C).f1 12782 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12782 163 ∧
    0 ≤ (tableEnvelope C).w1 12782 163 ∧ 0 ≤ (tableEnvelope C).w2 12782 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12782 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12782 163 ∧ 0 ≤ d.f1 12782 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12782 163 ∧ 0 ≤ d.w1 12782 163 ∧ 0 ≤ d.w2 12782 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12782 ≤ 2 * (228 / 100 : ℝ) / 12782 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12782 ≤ 2 * (370 / 100 : ℝ) / 12782 := by
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
    (completeRAData (tableEnvelope C) 12782 163).locationBound 12782 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12782 163).energyBound 12782 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12782 163) (d.f1 12782 163) d.f2 ≤
      32 * (((4509551343 / 1000000000000000000) : ℝ) + (1504462817 / 1000000000000000000) + (2259989 / 6250000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12782 163) (d.w1 12782 163)
      (d.w2 12782 163) ≤
      32 * (((1798141571 / 100000000000000000000) : ℝ) + (639671723 / 50000000000000000000) + (18697593 / 4000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12782 163) (d.f1 12782 163) d.f2 ≤
      ((4509551343 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4509551343 / 1000000000000000000)) * ((1504462817 / 1000000000000000000)) * (126 / 100) +
      2 * (((1504462817 / 1000000000000000000)) ^ 2 + 2 * ((4509551343 / 1000000000000000000)) * ((2259989 / 6250000000000000))) +
      6 * ((1504462817 / 1000000000000000000)) * ((2259989 / 6250000000000000)) * (126 / 100) + 8 * ((2259989 / 6250000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12782 163) (d.f1 12782 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12782 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12782 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12782 163) (d.f1 12782 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12782 163) (d.w1 12782 163) (d.w2 12782 163)
  have hwexpr0 : 0 ≤ d.w0 12782 163 + d.w1 12782 163 * √(π / 2) +
      2 * d.w2 12782 163 + energyR16 12782 *
      radiusPolynomialRoot16 (d.w0 12782 163) (d.w1 12782 163) (d.w2 12782 163) := by
    positivity
  constructor
  · change (12782 : ℝ) ^ 8 * (mA 12782 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12782 163) (d.f1 12782 163) d.f2 + locationR16 12782 *
        radiusPolynomialRoot16 (d.f0 12782 163) (d.f1 12782 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12782 : ℝ) ^ 8 * (mA 12782 : ℝ) ^ 8 *
        ((((4509551343 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4509551343 / 1000000000000000000)) * ((1504462817 / 1000000000000000000)) * (126 / 100) +
          2 * (((1504462817 / 1000000000000000000)) ^ 2 + 2 * ((4509551343 / 1000000000000000000)) * ((2259989 / 6250000000000000))) +
          6 * ((1504462817 / 1000000000000000000)) * ((2259989 / 6250000000000000)) * (126 / 100) + 8 * ((2259989 / 6250000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12782) *
          (32 * (((4509551343 / 1000000000000000000) : ℝ) + (1504462817 / 1000000000000000000) + (2259989 / 6250000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12782 : ℝ) ^ 16 *
      (d.w0 12782 163 + d.w1 12782 163 * √(π / 2) + 2 * d.w2 12782 163 +
        energyR16 12782 * radiusPolynomialRoot16 (d.w0 12782 163) (d.w1 12782 163)
          (d.w2 12782 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12782 : ℝ) ^ 16 *
        (((1798141571 / 100000000000000000000) : ℝ) + ((639671723 / 50000000000000000000)) * (126 / 100) + 2 * ((18697593 / 4000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12782) *
          (32 * (((1798141571 / 100000000000000000000) : ℝ) + (639671723 / 50000000000000000000) + (18697593 / 4000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12782

/-! A coarse bound on the actual paper statistics constant at dimension 12783. -/
namespace BstLean.Part266.Row12783
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12781 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12781 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12781 128 ≤ (13035 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13035 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12783) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12783 : ℕ))
    (by norm_num : (12783 : ℕ) ≤ 16384)
  have ht : paperTail256 12783 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12783 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12783 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12783 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12783 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12783 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12781 128 * √(2 / (12783 : ℝ)) *
      (√(12783 : ℝ) + paperT0 12783 + paperTail256 12783) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12783 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12783 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12783 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12781 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12781 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12783 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12783

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12783
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12783 (61 / 100) 163 (17 / (100 * 12783)) (26 / (10 * 12783)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12783 (61 / 100) 163 (17 / (100 * 12783)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (467325421 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (731167061 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (606893889 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12783 / 12783 * (61 / 100)) ^ 4 * inverseRadius8 (12783 - 1) /
            envelopeGap 12783 (61 / 100) 163 (17 / (100 * 12783)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12783

namespace BstLean.Part266.Row12783
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12783 163 ≤ (2254335323 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12783 163 ≤ (12033351 / 8000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (90381889 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12783 163 ≤ (1797719837 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12783 163 ≤ (319760833 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12783 163 ≤ (3738641 / 800000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (467325421 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (467325421 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (731167061 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (606893889 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3646767 / 1000000000) : ℝ) ≤ √(17 / (100 * 12783) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12783) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1080885541 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19120238767 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12783) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12783) ≤ (110632369 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12783) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12783 * (163 : ℝ) ^ 2 + 26 / (10 * 12783) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12783) : ℝ)) (tA 12783 * 163 ^ 2 + 26 / (10 * 12783)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3646767 / 1000000000))) * ((467325421 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3646767 / 1000000000)) ^ 3) * ((731167061 / 500000000000000000000000))) + ((606893889 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3646767 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12783) : ℝ)) d.D d.V d.P (√(tA 12783) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3646767 / 1000000000)) ^ 2 * (((1080885541 / 500000000000000)) * ((19120238767 / 500000000000000000)))) + ((606893889 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12783) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3646767 / 1000000000)) * ((467325421 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12783) : ℝ)) (tA 12783 * 163 ^ 2 + 26 / (10 * 12783)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((467325421 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3646767 / 1000000000)) ^ 2) * ((731167061 / 500000000000000000000000)) + ((606893889 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12783) : ℝ)) (√(26 / (10 * 12783) : ℝ)) d.D d.V d.P (√(tA 12783) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3646767 / 1000000000)) * (((1080885541 / 500000000000000)) * ((19120238767 / 500000000000000000))) + ((606893889 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12783) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((467325421 / 100000000000000000000) : ℝ) + ((606893889 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12783

namespace BstLean.Part266.Row12783
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12783 163 ∧
    0 ≤ (tableEnvelope C).f1 12783 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12783 163 ∧
    0 ≤ (tableEnvelope C).w1 12783 163 ∧ 0 ≤ (tableEnvelope C).w2 12783 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12783 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12783 163 ∧ 0 ≤ d.f1 12783 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12783 163 ∧ 0 ≤ d.w1 12783 163 ∧ 0 ≤ d.w2 12783 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12783 ≤ 2 * (228 / 100 : ℝ) / 12783 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12783 ≤ 2 * (370 / 100 : ℝ) / 12783 := by
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
    (completeRAData (tableEnvelope C) 12783 163).locationBound 12783 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12783 163).energyBound 12783 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12783 163) (d.f1 12783 163) d.f2 ≤
      32 * (((2254335323 / 500000000000000000) : ℝ) + (12033351 / 8000000000000000) + (90381889 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12783 163) (d.w1 12783 163)
      (d.w2 12783 163) ≤
      32 * (((1797719837 / 100000000000000000000) : ℝ) + (319760833 / 25000000000000000000) + (3738641 / 800000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12783 163) (d.f1 12783 163) d.f2 ≤
      ((2254335323 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2254335323 / 500000000000000000)) * ((12033351 / 8000000000000000)) * (126 / 100) +
      2 * (((12033351 / 8000000000000000)) ^ 2 + 2 * ((2254335323 / 500000000000000000)) * ((90381889 / 250000000000000000))) +
      6 * ((12033351 / 8000000000000000)) * ((90381889 / 250000000000000000)) * (126 / 100) + 8 * ((90381889 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12783 163) (d.f1 12783 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12783 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12783 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12783 163) (d.f1 12783 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12783 163) (d.w1 12783 163) (d.w2 12783 163)
  have hwexpr0 : 0 ≤ d.w0 12783 163 + d.w1 12783 163 * √(π / 2) +
      2 * d.w2 12783 163 + energyR16 12783 *
      radiusPolynomialRoot16 (d.w0 12783 163) (d.w1 12783 163) (d.w2 12783 163) := by
    positivity
  constructor
  · change (12783 : ℝ) ^ 8 * (mA 12783 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12783 163) (d.f1 12783 163) d.f2 + locationR16 12783 *
        radiusPolynomialRoot16 (d.f0 12783 163) (d.f1 12783 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12783 : ℝ) ^ 8 * (mA 12783 : ℝ) ^ 8 *
        ((((2254335323 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2254335323 / 500000000000000000)) * ((12033351 / 8000000000000000)) * (126 / 100) +
          2 * (((12033351 / 8000000000000000)) ^ 2 + 2 * ((2254335323 / 500000000000000000)) * ((90381889 / 250000000000000000))) +
          6 * ((12033351 / 8000000000000000)) * ((90381889 / 250000000000000000)) * (126 / 100) + 8 * ((90381889 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12783) *
          (32 * (((2254335323 / 500000000000000000) : ℝ) + (12033351 / 8000000000000000) + (90381889 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12783 : ℝ) ^ 16 *
      (d.w0 12783 163 + d.w1 12783 163 * √(π / 2) + 2 * d.w2 12783 163 +
        energyR16 12783 * radiusPolynomialRoot16 (d.w0 12783 163) (d.w1 12783 163)
          (d.w2 12783 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12783 : ℝ) ^ 16 *
        (((1797719837 / 100000000000000000000) : ℝ) + ((319760833 / 25000000000000000000)) * (126 / 100) + 2 * ((3738641 / 800000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12783) *
          (32 * (((1797719837 / 100000000000000000000) : ℝ) + (319760833 / 25000000000000000000) + (3738641 / 800000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12783

/-! A coarse bound on the actual paper statistics constant at dimension 12784. -/
namespace BstLean.Part266.Row12784
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12782 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12782 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12782 128 ≤ (13036 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13036 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12784) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12784 : ℕ))
    (by norm_num : (12784 : ℕ) ≤ 16384)
  have ht : paperTail256 12784 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12784 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12784 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12784 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12784 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12784 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12782 128 * √(2 / (12784 : ℝ)) *
      (√(12784 : ℝ) + paperT0 12784 + paperTail256 12784) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12784 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12784 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12784 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12782 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12782 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12784 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12784

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12784
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12784 (61 / 100) 163 (17 / (100 * 12784)) (26 / (10 * 12784)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12784 (61 / 100) 163 (17 / (100 * 12784)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (467215757 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1461876607 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4852084481 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12784 / 12784 * (61 / 100)) ^ 4 * inverseRadius8 (12784 - 1) /
            envelopeGap 12784 (61 / 100) 163 (17 / (100 * 12784)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12784

namespace BstLean.Part266.Row12784
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12784 163 ≤ (4507790251 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12784 163 ≤ (60155001 / 40000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (361456893 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12784 163 ≤ (224662281 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12784 163 ≤ (639371659 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12784 163 ≤ (233610229 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (467215757 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (467215757 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1461876607 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4852084481 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((113957 / 31250000) : ℝ) ≤ √(17 / (100 * 12784) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12784) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (135094839 / 62500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38234494989 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12784) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12784) ≤ (22124743 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12784) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12784 * (163 : ℝ) ^ 2 + 26 / (10 * 12784) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12784) : ℝ)) (tA 12784 * 163 ^ 2 + 26 / (10 * 12784)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((113957 / 31250000))) * ((467215757 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((113957 / 31250000)) ^ 3) * ((1461876607 / 1000000000000000000000000))) + ((4852084481 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((113957 / 31250000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12784) : ℝ)) d.D d.V d.P (√(tA 12784) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((113957 / 31250000)) ^ 2 * (((135094839 / 62500000000000)) * ((38234494989 / 1000000000000000000)))) + ((4852084481 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12784) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((113957 / 31250000)) * ((467215757 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12784) : ℝ)) (tA 12784 * 163 ^ 2 + 26 / (10 * 12784)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((467215757 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((113957 / 31250000)) ^ 2) * ((1461876607 / 1000000000000000000000000)) + ((4852084481 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12784) : ℝ)) (√(26 / (10 * 12784) : ℝ)) d.D d.V d.P (√(tA 12784) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((113957 / 31250000)) * (((135094839 / 62500000000000)) * ((38234494989 / 1000000000000000000))) + ((4852084481 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12784) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((467215757 / 100000000000000000000) : ℝ) + ((4852084481 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12784

namespace BstLean.Part266.Row12784
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12784 163 ∧
    0 ≤ (tableEnvelope C).f1 12784 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12784 163 ∧
    0 ≤ (tableEnvelope C).w1 12784 163 ∧ 0 ≤ (tableEnvelope C).w2 12784 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12784 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12784 163 ∧ 0 ≤ d.f1 12784 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12784 163 ∧ 0 ≤ d.w1 12784 163 ∧ 0 ≤ d.w2 12784 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12784 ≤ 2 * (228 / 100 : ℝ) / 12784 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12784 ≤ 2 * (370 / 100 : ℝ) / 12784 := by
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
    (completeRAData (tableEnvelope C) 12784 163).locationBound 12784 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12784 163).energyBound 12784 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12784 163) (d.f1 12784 163) d.f2 ≤
      32 * (((4507790251 / 1000000000000000000) : ℝ) + (60155001 / 40000000000000000) + (361456893 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12784 163) (d.w1 12784 163)
      (d.w2 12784 163) ≤
      32 * (((224662281 / 12500000000000000000) : ℝ) + (639371659 / 50000000000000000000) + (233610229 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12784 163) (d.f1 12784 163) d.f2 ≤
      ((4507790251 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4507790251 / 1000000000000000000)) * ((60155001 / 40000000000000000)) * (126 / 100) +
      2 * (((60155001 / 40000000000000000)) ^ 2 + 2 * ((4507790251 / 1000000000000000000)) * ((361456893 / 1000000000000000000))) +
      6 * ((60155001 / 40000000000000000)) * ((361456893 / 1000000000000000000)) * (126 / 100) + 8 * ((361456893 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12784 163) (d.f1 12784 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12784 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12784 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12784 163) (d.f1 12784 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12784 163) (d.w1 12784 163) (d.w2 12784 163)
  have hwexpr0 : 0 ≤ d.w0 12784 163 + d.w1 12784 163 * √(π / 2) +
      2 * d.w2 12784 163 + energyR16 12784 *
      radiusPolynomialRoot16 (d.w0 12784 163) (d.w1 12784 163) (d.w2 12784 163) := by
    positivity
  constructor
  · change (12784 : ℝ) ^ 8 * (mA 12784 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12784 163) (d.f1 12784 163) d.f2 + locationR16 12784 *
        radiusPolynomialRoot16 (d.f0 12784 163) (d.f1 12784 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12784 : ℝ) ^ 8 * (mA 12784 : ℝ) ^ 8 *
        ((((4507790251 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4507790251 / 1000000000000000000)) * ((60155001 / 40000000000000000)) * (126 / 100) +
          2 * (((60155001 / 40000000000000000)) ^ 2 + 2 * ((4507790251 / 1000000000000000000)) * ((361456893 / 1000000000000000000))) +
          6 * ((60155001 / 40000000000000000)) * ((361456893 / 1000000000000000000)) * (126 / 100) + 8 * ((361456893 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12784) *
          (32 * (((4507790251 / 1000000000000000000) : ℝ) + (60155001 / 40000000000000000) + (361456893 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12784 : ℝ) ^ 16 *
      (d.w0 12784 163 + d.w1 12784 163 * √(π / 2) + 2 * d.w2 12784 163 +
        energyR16 12784 * radiusPolynomialRoot16 (d.w0 12784 163) (d.w1 12784 163)
          (d.w2 12784 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12784 : ℝ) ^ 16 *
        (((224662281 / 12500000000000000000) : ℝ) + ((639371659 / 50000000000000000000)) * (126 / 100) + 2 * ((233610229 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12784) *
          (32 * (((224662281 / 12500000000000000000) : ℝ) + (639371659 / 50000000000000000000) + (233610229 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12784

/-! A coarse bound on the actual paper statistics constant at dimension 12785. -/
namespace BstLean.Part266.Row12785
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12783 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12783 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12783 128 ≤ (13037 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13037 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12785) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12785 : ℕ))
    (by norm_num : (12785 : ℕ) ≤ 16384)
  have ht : paperTail256 12785 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12785 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12785 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12785 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12785 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12785 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12783 128 * √(2 / (12785 : ℝ)) *
      (√(12785 : ℝ) + paperT0 12785 + paperTail256 12785) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12785 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12785 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12785 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12783 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12783 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12785 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12785

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12785
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12785 (61 / 100) 163 (17 / (100 * 12785)) (26 / (10 * 12785)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12785 (61 / 100) 163 (17 / (100 * 12785)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (29194133 / 6250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (146141927 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4849020031 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12785 / 12785 * (61 / 100)) ^ 4 * inverseRadius8 (12785 - 1) /
            envelopeGap 12785 (61 / 100) 163 (17 / (100 * 12785)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12785

namespace BstLean.Part266.Row12785
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12785 163 ≤ (1126726647 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12785 163 ≤ (751790223 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (45173269 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12785 163 ≤ (1796876073 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12785 163 ≤ (319610763 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12785 163 ≤ (233555413 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (29194133 / 6250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (29194133 / 6250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (146141927 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4849020031 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1823241 / 500000000) : ℝ) ≤ √(17 / (100 * 12785) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12785) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (270157977 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7645702767 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12785) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12785) ≤ (55307531 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12785) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12785 * (163 : ℝ) ^ 2 + 26 / (10 * 12785) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12785) : ℝ)) (tA 12785 * 163 ^ 2 + 26 / (10 * 12785)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1823241 / 500000000))) * ((29194133 / 6250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1823241 / 500000000)) ^ 3) * ((146141927 / 100000000000000000000000))) + ((4849020031 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1823241 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12785) : ℝ)) d.D d.V d.P (√(tA 12785) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1823241 / 500000000)) ^ 2 * (((270157977 / 125000000000000)) * ((7645702767 / 200000000000000000)))) + ((4849020031 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12785) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1823241 / 500000000)) * ((29194133 / 6250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12785) : ℝ)) (tA 12785 * 163 ^ 2 + 26 / (10 * 12785)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((29194133 / 6250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1823241 / 500000000)) ^ 2) * ((146141927 / 100000000000000000000000)) + ((4849020031 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12785) : ℝ)) (√(26 / (10 * 12785) : ℝ)) d.D d.V d.P (√(tA 12785) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1823241 / 500000000)) * (((270157977 / 125000000000000)) * ((7645702767 / 200000000000000000))) + ((4849020031 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12785) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((29194133 / 6250000000000000000) : ℝ) + ((4849020031 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12785

namespace BstLean.Part266.Row12785
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12785 163 ∧
    0 ≤ (tableEnvelope C).f1 12785 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12785 163 ∧
    0 ≤ (tableEnvelope C).w1 12785 163 ∧ 0 ≤ (tableEnvelope C).w2 12785 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12785 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12785 163 ∧ 0 ≤ d.f1 12785 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12785 163 ∧ 0 ≤ d.w1 12785 163 ∧ 0 ≤ d.w2 12785 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12785 ≤ 2 * (228 / 100 : ℝ) / 12785 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12785 ≤ 2 * (370 / 100 : ℝ) / 12785 := by
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
    (completeRAData (tableEnvelope C) 12785 163).locationBound 12785 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12785 163).energyBound 12785 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12785 163) (d.f1 12785 163) d.f2 ≤
      32 * (((1126726647 / 250000000000000000) : ℝ) + (751790223 / 500000000000000000) + (45173269 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12785 163) (d.w1 12785 163)
      (d.w2 12785 163) ≤
      32 * (((1796876073 / 100000000000000000000) : ℝ) + (319610763 / 25000000000000000000) + (233555413 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12785 163) (d.f1 12785 163) d.f2 ≤
      ((1126726647 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1126726647 / 250000000000000000)) * ((751790223 / 500000000000000000)) * (126 / 100) +
      2 * (((751790223 / 500000000000000000)) ^ 2 + 2 * ((1126726647 / 250000000000000000)) * ((45173269 / 125000000000000000))) +
      6 * ((751790223 / 500000000000000000)) * ((45173269 / 125000000000000000)) * (126 / 100) + 8 * ((45173269 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12785 163) (d.f1 12785 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12785 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12785 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12785 163) (d.f1 12785 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12785 163) (d.w1 12785 163) (d.w2 12785 163)
  have hwexpr0 : 0 ≤ d.w0 12785 163 + d.w1 12785 163 * √(π / 2) +
      2 * d.w2 12785 163 + energyR16 12785 *
      radiusPolynomialRoot16 (d.w0 12785 163) (d.w1 12785 163) (d.w2 12785 163) := by
    positivity
  constructor
  · change (12785 : ℝ) ^ 8 * (mA 12785 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12785 163) (d.f1 12785 163) d.f2 + locationR16 12785 *
        radiusPolynomialRoot16 (d.f0 12785 163) (d.f1 12785 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12785 : ℝ) ^ 8 * (mA 12785 : ℝ) ^ 8 *
        ((((1126726647 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1126726647 / 250000000000000000)) * ((751790223 / 500000000000000000)) * (126 / 100) +
          2 * (((751790223 / 500000000000000000)) ^ 2 + 2 * ((1126726647 / 250000000000000000)) * ((45173269 / 125000000000000000))) +
          6 * ((751790223 / 500000000000000000)) * ((45173269 / 125000000000000000)) * (126 / 100) + 8 * ((45173269 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12785) *
          (32 * (((1126726647 / 250000000000000000) : ℝ) + (751790223 / 500000000000000000) + (45173269 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12785 : ℝ) ^ 16 *
      (d.w0 12785 163 + d.w1 12785 163 * √(π / 2) + 2 * d.w2 12785 163 +
        energyR16 12785 * radiusPolynomialRoot16 (d.w0 12785 163) (d.w1 12785 163)
          (d.w2 12785 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12785 : ℝ) ^ 16 *
        (((1796876073 / 100000000000000000000) : ℝ) + ((319610763 / 25000000000000000000)) * (126 / 100) + 2 * ((233555413 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12785) *
          (32 * (((1796876073 / 100000000000000000000) : ℝ) + (319610763 / 25000000000000000000) + (233555413 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12785

/-! A coarse bound on the actual paper statistics constant at dimension 12786. -/
namespace BstLean.Part266.Row12786
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12784 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12784 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12784 128 ≤ (13038 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13038 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12786) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12786 : ℕ))
    (by norm_num : (12786 : ℕ) ≤ 16384)
  have ht : paperTail256 12786 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12786 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12786 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12786 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12786 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12786 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12784 128 * √(2 / (12786 : ℝ)) *
      (√(12786 : ℝ) + paperT0 12786 + paperTail256 12786) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12786 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12786 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12786 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12784 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12784 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12786 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12786

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12786
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12786 (61 / 100) 163 (17 / (100 * 12786)) (26 / (10 * 12786)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12786 (61 / 100) 163 (17 / (100 * 12786)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (466996533 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (22827533 / 15625000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (7571809 / 1562500000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12786 / 12786 * (61 / 100)) ^ 4 * inverseRadius8 (12786 - 1) /
            envelopeGap 12786 (61 / 100) 163 (17 / (100 * 12786)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12786

namespace BstLean.Part266.Row12786
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12786 163 ≤ (2253013397 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12786 163 ≤ (300657357 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (361315531 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12786 163 ≤ (449113693 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12786 163 ≤ (1278143237 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12786 163 ≤ (116750307 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (466996533 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (466996533 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (22827533 / 15625000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (7571809 / 1562500000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3646339 / 1000000000) : ℝ) ≤ √(17 / (100 * 12786) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12786) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2161010257 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38222534087 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12786) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12786) ≤ (110606411 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12786) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12786 * (163 : ℝ) ^ 2 + 26 / (10 * 12786) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12786) : ℝ)) (tA 12786 * 163 ^ 2 + 26 / (10 * 12786)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3646339 / 1000000000))) * ((466996533 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3646339 / 1000000000)) ^ 3) * ((22827533 / 15625000000000000000000))) + ((7571809 / 1562500000000000000000)) * (3 / 2 * (39895 / 100000) / ((3646339 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12786) : ℝ)) d.D d.V d.P (√(tA 12786) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3646339 / 1000000000)) ^ 2 * (((2161010257 / 1000000000000000)) * ((38222534087 / 1000000000000000000)))) + ((7571809 / 1562500000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12786) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3646339 / 1000000000)) * ((466996533 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12786) : ℝ)) (tA 12786 * 163 ^ 2 + 26 / (10 * 12786)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((466996533 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3646339 / 1000000000)) ^ 2) * ((22827533 / 15625000000000000000000)) + ((7571809 / 1562500000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12786) : ℝ)) (√(26 / (10 * 12786) : ℝ)) d.D d.V d.P (√(tA 12786) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3646339 / 1000000000)) * (((2161010257 / 1000000000000000)) * ((38222534087 / 1000000000000000000))) + ((7571809 / 1562500000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12786) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((466996533 / 100000000000000000000) : ℝ) + ((7571809 / 1562500000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12786

namespace BstLean.Part266.Row12786
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12786 163 ∧
    0 ≤ (tableEnvelope C).f1 12786 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12786 163 ∧
    0 ≤ (tableEnvelope C).w1 12786 163 ∧ 0 ≤ (tableEnvelope C).w2 12786 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12786 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12786 163 ∧ 0 ≤ d.f1 12786 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12786 163 ∧ 0 ≤ d.w1 12786 163 ∧ 0 ≤ d.w2 12786 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12786 ≤ 2 * (228 / 100 : ℝ) / 12786 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12786 ≤ 2 * (370 / 100 : ℝ) / 12786 := by
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
    (completeRAData (tableEnvelope C) 12786 163).locationBound 12786 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12786 163).energyBound 12786 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12786 163) (d.f1 12786 163) d.f2 ≤
      32 * (((2253013397 / 500000000000000000) : ℝ) + (300657357 / 200000000000000000) + (361315531 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12786 163) (d.w1 12786 163)
      (d.w2 12786 163) ≤
      32 * (((449113693 / 25000000000000000000) : ℝ) + (1278143237 / 100000000000000000000) + (116750307 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12786 163) (d.f1 12786 163) d.f2 ≤
      ((2253013397 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2253013397 / 500000000000000000)) * ((300657357 / 200000000000000000)) * (126 / 100) +
      2 * (((300657357 / 200000000000000000)) ^ 2 + 2 * ((2253013397 / 500000000000000000)) * ((361315531 / 1000000000000000000))) +
      6 * ((300657357 / 200000000000000000)) * ((361315531 / 1000000000000000000)) * (126 / 100) + 8 * ((361315531 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12786 163) (d.f1 12786 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12786 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12786 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12786 163) (d.f1 12786 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12786 163) (d.w1 12786 163) (d.w2 12786 163)
  have hwexpr0 : 0 ≤ d.w0 12786 163 + d.w1 12786 163 * √(π / 2) +
      2 * d.w2 12786 163 + energyR16 12786 *
      radiusPolynomialRoot16 (d.w0 12786 163) (d.w1 12786 163) (d.w2 12786 163) := by
    positivity
  constructor
  · change (12786 : ℝ) ^ 8 * (mA 12786 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12786 163) (d.f1 12786 163) d.f2 + locationR16 12786 *
        radiusPolynomialRoot16 (d.f0 12786 163) (d.f1 12786 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12786 : ℝ) ^ 8 * (mA 12786 : ℝ) ^ 8 *
        ((((2253013397 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2253013397 / 500000000000000000)) * ((300657357 / 200000000000000000)) * (126 / 100) +
          2 * (((300657357 / 200000000000000000)) ^ 2 + 2 * ((2253013397 / 500000000000000000)) * ((361315531 / 1000000000000000000))) +
          6 * ((300657357 / 200000000000000000)) * ((361315531 / 1000000000000000000)) * (126 / 100) + 8 * ((361315531 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12786) *
          (32 * (((2253013397 / 500000000000000000) : ℝ) + (300657357 / 200000000000000000) + (361315531 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12786 : ℝ) ^ 16 *
      (d.w0 12786 163 + d.w1 12786 163 * √(π / 2) + 2 * d.w2 12786 163 +
        energyR16 12786 * radiusPolynomialRoot16 (d.w0 12786 163) (d.w1 12786 163)
          (d.w2 12786 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12786 : ℝ) ^ 16 *
        (((449113693 / 25000000000000000000) : ℝ) + ((1278143237 / 100000000000000000000)) * (126 / 100) + 2 * ((116750307 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12786) *
          (32 * (((449113693 / 25000000000000000000) : ℝ) + (1278143237 / 100000000000000000000) + (116750307 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12786

/-! A coarse bound on the actual paper statistics constant at dimension 12787. -/
namespace BstLean.Part266.Row12787
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12785 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12785 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12785 128 ≤ (13039 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13039 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12787) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12787 : ℕ))
    (by norm_num : (12787 : ℕ) ≤ 16384)
  have ht : paperTail256 12787 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12787 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12787 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12787 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12787 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12787 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12785 128 * √(2 / (12787 : ℝ)) *
      (√(12787 : ℝ) + paperT0 12787 + paperTail256 12787) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12787 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12787 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12787 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12785 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12785 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12787 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12787

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12787
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12787 (61 / 100) 163 (17 / (100 * 12787)) (26 / (10 * 12787)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12787 (61 / 100) 163 (17 / (100 * 12787)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (116721743 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1460505133 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4842897667 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12787 / 12787 * (61 / 100)) ^ 4 * inverseRadius8 (12787 - 1) /
            envelopeGap 12787 (61 / 100) 163 (17 / (100 * 12787)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12787

namespace BstLean.Part266.Row12787
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12787 163 ≤ (45051473 / 10000000000000000)
  f1 : (tableEnvelope C).f1 12787 163 ≤ (751496609 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (36124493 / 100000000000000000)
  w0 : (tableEnvelope C).w0 12787 163 ≤ (898016807 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12787 163 ≤ (1277843521 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12787 163 ≤ (29180729 / 6250000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (116721743 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (116721743 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1460505133 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4842897667 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((911549 / 250000000) : ℝ) ≤ √(17 / (100 * 12787) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12787) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (540189187 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7643311149 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12787) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12787) ≤ (110597761 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12787) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12787 * (163 : ℝ) ^ 2 + 26 / (10 * 12787) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12787) : ℝ)) (tA 12787 * 163 ^ 2 + 26 / (10 * 12787)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((911549 / 250000000))) * ((116721743 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((911549 / 250000000)) ^ 3) * ((1460505133 / 1000000000000000000000000))) + ((4842897667 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((911549 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12787) : ℝ)) d.D d.V d.P (√(tA 12787) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((911549 / 250000000)) ^ 2 * (((540189187 / 250000000000000)) * ((7643311149 / 200000000000000000)))) + ((4842897667 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12787) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((911549 / 250000000)) * ((116721743 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12787) : ℝ)) (tA 12787 * 163 ^ 2 + 26 / (10 * 12787)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((116721743 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((911549 / 250000000)) ^ 2) * ((1460505133 / 1000000000000000000000000)) + ((4842897667 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12787) : ℝ)) (√(26 / (10 * 12787) : ℝ)) d.D d.V d.P (√(tA 12787) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((911549 / 250000000)) * (((540189187 / 250000000000000)) * ((7643311149 / 200000000000000000))) + ((4842897667 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12787) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((116721743 / 25000000000000000000) : ℝ) + ((4842897667 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12787

namespace BstLean.Part266.Row12787
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12787 163 ∧
    0 ≤ (tableEnvelope C).f1 12787 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12787 163 ∧
    0 ≤ (tableEnvelope C).w1 12787 163 ∧ 0 ≤ (tableEnvelope C).w2 12787 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12787 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12787 163 ∧ 0 ≤ d.f1 12787 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12787 163 ∧ 0 ≤ d.w1 12787 163 ∧ 0 ≤ d.w2 12787 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12787 ≤ 2 * (228 / 100 : ℝ) / 12787 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12787 ≤ 2 * (370 / 100 : ℝ) / 12787 := by
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
    (completeRAData (tableEnvelope C) 12787 163).locationBound 12787 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12787 163).energyBound 12787 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12787 163) (d.f1 12787 163) d.f2 ≤
      32 * (((45051473 / 10000000000000000) : ℝ) + (751496609 / 500000000000000000) + (36124493 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12787 163) (d.w1 12787 163)
      (d.w2 12787 163) ≤
      32 * (((898016807 / 50000000000000000000) : ℝ) + (1277843521 / 100000000000000000000) + (29180729 / 6250000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12787 163) (d.f1 12787 163) d.f2 ≤
      ((45051473 / 10000000000000000) : ℝ) ^ 2 + 2 * ((45051473 / 10000000000000000)) * ((751496609 / 500000000000000000)) * (126 / 100) +
      2 * (((751496609 / 500000000000000000)) ^ 2 + 2 * ((45051473 / 10000000000000000)) * ((36124493 / 100000000000000000))) +
      6 * ((751496609 / 500000000000000000)) * ((36124493 / 100000000000000000)) * (126 / 100) + 8 * ((36124493 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12787 163) (d.f1 12787 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12787 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12787 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12787 163) (d.f1 12787 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12787 163) (d.w1 12787 163) (d.w2 12787 163)
  have hwexpr0 : 0 ≤ d.w0 12787 163 + d.w1 12787 163 * √(π / 2) +
      2 * d.w2 12787 163 + energyR16 12787 *
      radiusPolynomialRoot16 (d.w0 12787 163) (d.w1 12787 163) (d.w2 12787 163) := by
    positivity
  constructor
  · change (12787 : ℝ) ^ 8 * (mA 12787 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12787 163) (d.f1 12787 163) d.f2 + locationR16 12787 *
        radiusPolynomialRoot16 (d.f0 12787 163) (d.f1 12787 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12787 : ℝ) ^ 8 * (mA 12787 : ℝ) ^ 8 *
        ((((45051473 / 10000000000000000) : ℝ) ^ 2 + 2 * ((45051473 / 10000000000000000)) * ((751496609 / 500000000000000000)) * (126 / 100) +
          2 * (((751496609 / 500000000000000000)) ^ 2 + 2 * ((45051473 / 10000000000000000)) * ((36124493 / 100000000000000000))) +
          6 * ((751496609 / 500000000000000000)) * ((36124493 / 100000000000000000)) * (126 / 100) + 8 * ((36124493 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12787) *
          (32 * (((45051473 / 10000000000000000) : ℝ) + (751496609 / 500000000000000000) + (36124493 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12787 : ℝ) ^ 16 *
      (d.w0 12787 163 + d.w1 12787 163 * √(π / 2) + 2 * d.w2 12787 163 +
        energyR16 12787 * radiusPolynomialRoot16 (d.w0 12787 163) (d.w1 12787 163)
          (d.w2 12787 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12787 : ℝ) ^ 16 *
        (((898016807 / 50000000000000000000) : ℝ) + ((1277843521 / 100000000000000000000)) * (126 / 100) + 2 * ((29180729 / 6250000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12787) *
          (32 * (((898016807 / 50000000000000000000) : ℝ) + (1277843521 / 100000000000000000000) + (29180729 / 6250000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12787

/-! A coarse bound on the actual paper statistics constant at dimension 12788. -/
namespace BstLean.Part266.Row12788
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12786 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12786 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12786 128 ≤ (13040 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13040 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12788) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12788 : ℕ))
    (by norm_num : (12788 : ℕ) ≤ 16384)
  have ht : paperTail256 12788 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12788 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12788 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12788 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12788 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12788 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12786 128 * √(2 / (12788 : ℝ)) *
      (√(12788 : ℝ) + paperT0 12788 + paperTail256 12788) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12788 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12788 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12788 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12786 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12786 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12788 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12788

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12788
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12788 (61 / 100) 163 (17 / (100 * 12788)) (26 / (10 * 12788)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12788 (61 / 100) 163 (17 / (100 * 12788)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (93355489 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1460048333 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (19359359 / 4000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12788 / 12788 * (61 / 100)) ^ 4 * inverseRadius8 (12788 - 1) /
            envelopeGap 12788 (61 / 100) 163 (17 / (100 * 12788)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12788

namespace BstLean.Part266.Row12788
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12788 163 ≤ (2252132271 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12788 163 ≤ (1502698921 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (90293563 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12788 163 ≤ (56112871 / 3125000000000000000)
  w1 : (tableEnvelope C).w1 12788 163 ≤ (638771777 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12788 163 ≤ (233391067 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (93355489 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (93355489 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1460048333 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (19359359 / 4000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1823027 / 500000000) : ℝ) ≤ √(17 / (100 * 12788) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12788) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2160503287 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38210578811 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12788) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12788) ≤ (13823639 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12788) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12788 * (163 : ℝ) ^ 2 + 26 / (10 * 12788) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12788) : ℝ)) (tA 12788 * 163 ^ 2 + 26 / (10 * 12788)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1823027 / 500000000))) * ((93355489 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1823027 / 500000000)) ^ 3) * ((1460048333 / 1000000000000000000000000))) + ((19359359 / 4000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1823027 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12788) : ℝ)) d.D d.V d.P (√(tA 12788) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1823027 / 500000000)) ^ 2 * (((2160503287 / 1000000000000000)) * ((38210578811 / 1000000000000000000)))) + ((19359359 / 4000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12788) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1823027 / 500000000)) * ((93355489 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12788) : ℝ)) (tA 12788 * 163 ^ 2 + 26 / (10 * 12788)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((93355489 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1823027 / 500000000)) ^ 2) * ((1460048333 / 1000000000000000000000000)) + ((19359359 / 4000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12788) : ℝ)) (√(26 / (10 * 12788) : ℝ)) d.D d.V d.P (√(tA 12788) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1823027 / 500000000)) * (((2160503287 / 1000000000000000)) * ((38210578811 / 1000000000000000000))) + ((19359359 / 4000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12788) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((93355489 / 20000000000000000000) : ℝ) + ((19359359 / 4000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12788

namespace BstLean.Part266.Row12788
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12788 163 ∧
    0 ≤ (tableEnvelope C).f1 12788 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12788 163 ∧
    0 ≤ (tableEnvelope C).w1 12788 163 ∧ 0 ≤ (tableEnvelope C).w2 12788 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12788 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12788 163 ∧ 0 ≤ d.f1 12788 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12788 163 ∧ 0 ≤ d.w1 12788 163 ∧ 0 ≤ d.w2 12788 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12788 ≤ 2 * (228 / 100 : ℝ) / 12788 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12788 ≤ 2 * (370 / 100 : ℝ) / 12788 := by
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
    (completeRAData (tableEnvelope C) 12788 163).locationBound 12788 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12788 163).energyBound 12788 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12788 163) (d.f1 12788 163) d.f2 ≤
      32 * (((2252132271 / 500000000000000000) : ℝ) + (1502698921 / 1000000000000000000) + (90293563 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12788 163) (d.w1 12788 163)
      (d.w2 12788 163) ≤
      32 * (((56112871 / 3125000000000000000) : ℝ) + (638771777 / 50000000000000000000) + (233391067 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12788 163) (d.f1 12788 163) d.f2 ≤
      ((2252132271 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2252132271 / 500000000000000000)) * ((1502698921 / 1000000000000000000)) * (126 / 100) +
      2 * (((1502698921 / 1000000000000000000)) ^ 2 + 2 * ((2252132271 / 500000000000000000)) * ((90293563 / 250000000000000000))) +
      6 * ((1502698921 / 1000000000000000000)) * ((90293563 / 250000000000000000)) * (126 / 100) + 8 * ((90293563 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12788 163) (d.f1 12788 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12788 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12788 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12788 163) (d.f1 12788 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12788 163) (d.w1 12788 163) (d.w2 12788 163)
  have hwexpr0 : 0 ≤ d.w0 12788 163 + d.w1 12788 163 * √(π / 2) +
      2 * d.w2 12788 163 + energyR16 12788 *
      radiusPolynomialRoot16 (d.w0 12788 163) (d.w1 12788 163) (d.w2 12788 163) := by
    positivity
  constructor
  · change (12788 : ℝ) ^ 8 * (mA 12788 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12788 163) (d.f1 12788 163) d.f2 + locationR16 12788 *
        radiusPolynomialRoot16 (d.f0 12788 163) (d.f1 12788 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12788 : ℝ) ^ 8 * (mA 12788 : ℝ) ^ 8 *
        ((((2252132271 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2252132271 / 500000000000000000)) * ((1502698921 / 1000000000000000000)) * (126 / 100) +
          2 * (((1502698921 / 1000000000000000000)) ^ 2 + 2 * ((2252132271 / 500000000000000000)) * ((90293563 / 250000000000000000))) +
          6 * ((1502698921 / 1000000000000000000)) * ((90293563 / 250000000000000000)) * (126 / 100) + 8 * ((90293563 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12788) *
          (32 * (((2252132271 / 500000000000000000) : ℝ) + (1502698921 / 1000000000000000000) + (90293563 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12788 : ℝ) ^ 16 *
      (d.w0 12788 163 + d.w1 12788 163 * √(π / 2) + 2 * d.w2 12788 163 +
        energyR16 12788 * radiusPolynomialRoot16 (d.w0 12788 163) (d.w1 12788 163)
          (d.w2 12788 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12788 : ℝ) ^ 16 *
        (((56112871 / 3125000000000000000) : ℝ) + ((638771777 / 50000000000000000000)) * (126 / 100) + 2 * ((233391067 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12788) *
          (32 * (((56112871 / 3125000000000000000) : ℝ) + (638771777 / 50000000000000000000) + (233391067 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12788

/-! A coarse bound on the actual paper statistics constant at dimension 12789. -/
namespace BstLean.Part266.Row12789
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12787 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12787 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12787 128 ≤ (13041 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13041 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12789) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12789 : ℕ))
    (by norm_num : (12789 : ℕ) ≤ 16384)
  have ht : paperTail256 12789 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12789 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12789 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12789 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12789 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12789 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12787 128 * √(2 / (12789 : ℝ)) *
      (√(12789 : ℝ) + paperT0 12789 + paperTail256 12789) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12789 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12789 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12789 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12787 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12787 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12789 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12789

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12789
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12789 (61 / 100) 163 (17 / (100 * 12789)) (26 / (10 * 12789)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12789 (61 / 100) 163 (17 / (100 * 12789)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (466667953 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1459591711 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4836784007 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12789 / 12789 * (61 / 100)) ^ 4 * inverseRadius8 (12789 - 1) /
            envelopeGap 12789 (61 / 100) 163 (17 / (100 * 12789)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12789

namespace BstLean.Part266.Row12789
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12789 163 ≤ (4503385649 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12789 163 ≤ (751202771 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (180551847 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12789 163 ≤ (897595501 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12789 163 ≤ (1277244037 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12789 163 ≤ (466672639 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (466667953 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (466667953 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1459591711 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4836784007 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3645911 / 1000000000) : ℝ) ≤ √(17 / (100 * 12789) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12789) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2160249877 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3820460327 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12789) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12789) ≤ (22116093 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12789) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12789 * (163 : ℝ) ^ 2 + 26 / (10 * 12789) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12789) : ℝ)) (tA 12789 * 163 ^ 2 + 26 / (10 * 12789)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3645911 / 1000000000))) * ((466667953 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3645911 / 1000000000)) ^ 3) * ((1459591711 / 1000000000000000000000000))) + ((4836784007 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3645911 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12789) : ℝ)) d.D d.V d.P (√(tA 12789) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3645911 / 1000000000)) ^ 2 * (((2160249877 / 1000000000000000)) * ((3820460327 / 100000000000000000)))) + ((4836784007 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12789) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3645911 / 1000000000)) * ((466667953 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12789) : ℝ)) (tA 12789 * 163 ^ 2 + 26 / (10 * 12789)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((466667953 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3645911 / 1000000000)) ^ 2) * ((1459591711 / 1000000000000000000000000)) + ((4836784007 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12789) : ℝ)) (√(26 / (10 * 12789) : ℝ)) d.D d.V d.P (√(tA 12789) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3645911 / 1000000000)) * (((2160249877 / 1000000000000000)) * ((3820460327 / 100000000000000000))) + ((4836784007 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12789) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((466667953 / 100000000000000000000) : ℝ) + ((4836784007 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12789

namespace BstLean.Part266.Row12789
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12789 163 ∧
    0 ≤ (tableEnvelope C).f1 12789 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12789 163 ∧
    0 ≤ (tableEnvelope C).w1 12789 163 ∧ 0 ≤ (tableEnvelope C).w2 12789 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12789 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12789 163 ∧ 0 ≤ d.f1 12789 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12789 163 ∧ 0 ≤ d.w1 12789 163 ∧ 0 ≤ d.w2 12789 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12789 ≤ 2 * (228 / 100 : ℝ) / 12789 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12789 ≤ 2 * (370 / 100 : ℝ) / 12789 := by
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
    (completeRAData (tableEnvelope C) 12789 163).locationBound 12789 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12789 163).energyBound 12789 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12789 163) (d.f1 12789 163) d.f2 ≤
      32 * (((4503385649 / 1000000000000000000) : ℝ) + (751202771 / 500000000000000000) + (180551847 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12789 163) (d.w1 12789 163)
      (d.w2 12789 163) ≤
      32 * (((897595501 / 50000000000000000000) : ℝ) + (1277244037 / 100000000000000000000) + (466672639 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12789 163) (d.f1 12789 163) d.f2 ≤
      ((4503385649 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4503385649 / 1000000000000000000)) * ((751202771 / 500000000000000000)) * (126 / 100) +
      2 * (((751202771 / 500000000000000000)) ^ 2 + 2 * ((4503385649 / 1000000000000000000)) * ((180551847 / 500000000000000000))) +
      6 * ((751202771 / 500000000000000000)) * ((180551847 / 500000000000000000)) * (126 / 100) + 8 * ((180551847 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12789 163) (d.f1 12789 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12789 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12789 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12789 163) (d.f1 12789 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12789 163) (d.w1 12789 163) (d.w2 12789 163)
  have hwexpr0 : 0 ≤ d.w0 12789 163 + d.w1 12789 163 * √(π / 2) +
      2 * d.w2 12789 163 + energyR16 12789 *
      radiusPolynomialRoot16 (d.w0 12789 163) (d.w1 12789 163) (d.w2 12789 163) := by
    positivity
  constructor
  · change (12789 : ℝ) ^ 8 * (mA 12789 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12789 163) (d.f1 12789 163) d.f2 + locationR16 12789 *
        radiusPolynomialRoot16 (d.f0 12789 163) (d.f1 12789 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12789 : ℝ) ^ 8 * (mA 12789 : ℝ) ^ 8 *
        ((((4503385649 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4503385649 / 1000000000000000000)) * ((751202771 / 500000000000000000)) * (126 / 100) +
          2 * (((751202771 / 500000000000000000)) ^ 2 + 2 * ((4503385649 / 1000000000000000000)) * ((180551847 / 500000000000000000))) +
          6 * ((751202771 / 500000000000000000)) * ((180551847 / 500000000000000000)) * (126 / 100) + 8 * ((180551847 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12789) *
          (32 * (((4503385649 / 1000000000000000000) : ℝ) + (751202771 / 500000000000000000) + (180551847 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12789 : ℝ) ^ 16 *
      (d.w0 12789 163 + d.w1 12789 163 * √(π / 2) + 2 * d.w2 12789 163 +
        energyR16 12789 * radiusPolynomialRoot16 (d.w0 12789 163) (d.w1 12789 163)
          (d.w2 12789 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12789 : ℝ) ^ 16 *
        (((897595501 / 50000000000000000000) : ℝ) + ((1277244037 / 100000000000000000000)) * (126 / 100) + 2 * ((466672639 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12789) *
          (32 * (((897595501 / 50000000000000000000) : ℝ) + (1277244037 / 100000000000000000000) + (466672639 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12789

/-! A coarse bound on the actual paper statistics constant at dimension 12790. -/
namespace BstLean.Part266.Row12790
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12788 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12788 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12788 128 ≤ (13042 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13042 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12790) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12790 : ℕ))
    (by norm_num : (12790 : ℕ) ≤ 16384)
  have ht : paperTail256 12790 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12790 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12790 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12790 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12790 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12790 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12788 128 * √(2 / (12790 : ℝ)) *
      (√(12790 : ℝ) + paperT0 12790 + paperTail256 12790) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12790 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12790 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12790 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12788 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12788 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12790 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12790

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12790
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12790 (61 / 100) 163 (17 / (100 * 12790)) (26 / (10 * 12790)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12790 (61 / 100) 163 (17 / (100 * 12790)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (93311699 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (364783817 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4833730437 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12790 / 12790 * (61 / 100)) ^ 4 * inverseRadius8 (12790 - 1) /
            envelopeGap 12790 (61 / 100) 163 (17 / (100 * 12790)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12790

namespace BstLean.Part266.Row12790
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12790 163 ≤ (4502503493 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12790 163 ≤ (300422287 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (361033057 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12790 163 ≤ (448692387 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12790 163 ≤ (1276944271 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12790 163 ≤ (233281589 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (93311699 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (93311699 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (364783817 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4833730437 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3645769 / 1000000000) : ℝ) ≤ √(17 / (100 * 12790) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12790) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2159996517 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19099314569 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12790) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12790) ≤ (110571819 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12790) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12790 * (163 : ℝ) ^ 2 + 26 / (10 * 12790) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12790) : ℝ)) (tA 12790 * 163 ^ 2 + 26 / (10 * 12790)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3645769 / 1000000000))) * ((93311699 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3645769 / 1000000000)) ^ 3) * ((364783817 / 250000000000000000000000))) + ((4833730437 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3645769 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12790) : ℝ)) d.D d.V d.P (√(tA 12790) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3645769 / 1000000000)) ^ 2 * (((2159996517 / 1000000000000000)) * ((19099314569 / 500000000000000000)))) + ((4833730437 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12790) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3645769 / 1000000000)) * ((93311699 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12790) : ℝ)) (tA 12790 * 163 ^ 2 + 26 / (10 * 12790)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((93311699 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3645769 / 1000000000)) ^ 2) * ((364783817 / 250000000000000000000000)) + ((4833730437 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12790) : ℝ)) (√(26 / (10 * 12790) : ℝ)) d.D d.V d.P (√(tA 12790) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3645769 / 1000000000)) * (((2159996517 / 1000000000000000)) * ((19099314569 / 500000000000000000))) + ((4833730437 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12790) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((93311699 / 20000000000000000000) : ℝ) + ((4833730437 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12790

namespace BstLean.Part266.Row12790
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12790 163 ∧
    0 ≤ (tableEnvelope C).f1 12790 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12790 163 ∧
    0 ≤ (tableEnvelope C).w1 12790 163 ∧ 0 ≤ (tableEnvelope C).w2 12790 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12790 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12790 163 ∧ 0 ≤ d.f1 12790 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12790 163 ∧ 0 ≤ d.w1 12790 163 ∧ 0 ≤ d.w2 12790 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12790 ≤ 2 * (228 / 100 : ℝ) / 12790 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12790 ≤ 2 * (370 / 100 : ℝ) / 12790 := by
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
    (completeRAData (tableEnvelope C) 12790 163).locationBound 12790 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12790 163).energyBound 12790 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12790 163) (d.f1 12790 163) d.f2 ≤
      32 * (((4502503493 / 1000000000000000000) : ℝ) + (300422287 / 200000000000000000) + (361033057 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12790 163) (d.w1 12790 163)
      (d.w2 12790 163) ≤
      32 * (((448692387 / 25000000000000000000) : ℝ) + (1276944271 / 100000000000000000000) + (233281589 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12790 163) (d.f1 12790 163) d.f2 ≤
      ((4502503493 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4502503493 / 1000000000000000000)) * ((300422287 / 200000000000000000)) * (126 / 100) +
      2 * (((300422287 / 200000000000000000)) ^ 2 + 2 * ((4502503493 / 1000000000000000000)) * ((361033057 / 1000000000000000000))) +
      6 * ((300422287 / 200000000000000000)) * ((361033057 / 1000000000000000000)) * (126 / 100) + 8 * ((361033057 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12790 163) (d.f1 12790 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12790 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12790 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12790 163) (d.f1 12790 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12790 163) (d.w1 12790 163) (d.w2 12790 163)
  have hwexpr0 : 0 ≤ d.w0 12790 163 + d.w1 12790 163 * √(π / 2) +
      2 * d.w2 12790 163 + energyR16 12790 *
      radiusPolynomialRoot16 (d.w0 12790 163) (d.w1 12790 163) (d.w2 12790 163) := by
    positivity
  constructor
  · change (12790 : ℝ) ^ 8 * (mA 12790 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12790 163) (d.f1 12790 163) d.f2 + locationR16 12790 *
        radiusPolynomialRoot16 (d.f0 12790 163) (d.f1 12790 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12790 : ℝ) ^ 8 * (mA 12790 : ℝ) ^ 8 *
        ((((4502503493 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4502503493 / 1000000000000000000)) * ((300422287 / 200000000000000000)) * (126 / 100) +
          2 * (((300422287 / 200000000000000000)) ^ 2 + 2 * ((4502503493 / 1000000000000000000)) * ((361033057 / 1000000000000000000))) +
          6 * ((300422287 / 200000000000000000)) * ((361033057 / 1000000000000000000)) * (126 / 100) + 8 * ((361033057 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12790) *
          (32 * (((4502503493 / 1000000000000000000) : ℝ) + (300422287 / 200000000000000000) + (361033057 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12790 : ℝ) ^ 16 *
      (d.w0 12790 163 + d.w1 12790 163 * √(π / 2) + 2 * d.w2 12790 163 +
        energyR16 12790 * radiusPolynomialRoot16 (d.w0 12790 163) (d.w1 12790 163)
          (d.w2 12790 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12790 : ℝ) ^ 16 *
        (((448692387 / 25000000000000000000) : ℝ) + ((1276944271 / 100000000000000000000)) * (126 / 100) + 2 * ((233281589 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12790) *
          (32 * (((448692387 / 25000000000000000000) : ℝ) + (1276944271 / 100000000000000000000) + (233281589 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12790

/-! A coarse bound on the actual paper statistics constant at dimension 12791. -/
namespace BstLean.Part266.Row12791
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12789 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12789 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12789 128 ≤ (13043 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13043 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12791) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12791 : ℕ))
    (by norm_num : (12791 : ℕ) ≤ 16384)
  have ht : paperTail256 12791 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12791 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12791 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12791 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12791 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12791 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12789 128 * √(2 / (12791 : ℝ)) *
      (√(12791 : ℝ) + paperT0 12791 + paperTail256 12791) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12791 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12791 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12791 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12789 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12789 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12791 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12791

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12791
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12791 (61 / 100) 163 (17 / (100 * 12791)) (26 / (10 * 12791)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12791 (61 / 100) 163 (17 / (100 * 12791)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (466449071 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1458679003 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4830679037 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12791 / 12791 * (61 / 100)) ^ 4 * inverseRadius8 (12791 - 1) /
            envelopeGap 12791 (61 / 100) 163 (17 / (100 * 12791)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12791

namespace BstLean.Part266.Row12791
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12791 163 ≤ (4501625201 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12791 163 ≤ (375454561 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (360962541 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12791 163 ≤ (897174483 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12791 163 ≤ (1276644953 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12791 163 ≤ (466453751 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (466449071 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (466449071 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1458679003 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4830679037 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1822813 / 500000000) : ℝ) ≤ √(17 / (100 * 12791) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12791) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (431948641 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19096328201 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12791) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12791) ≤ (4422527 / 40000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12791) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12791 * (163 : ℝ) ^ 2 + 26 / (10 * 12791) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12791) : ℝ)) (tA 12791 * 163 ^ 2 + 26 / (10 * 12791)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1822813 / 500000000))) * ((466449071 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1822813 / 500000000)) ^ 3) * ((1458679003 / 1000000000000000000000000))) + ((4830679037 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1822813 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12791) : ℝ)) d.D d.V d.P (√(tA 12791) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1822813 / 500000000)) ^ 2 * (((431948641 / 200000000000000)) * ((19096328201 / 500000000000000000)))) + ((4830679037 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12791) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1822813 / 500000000)) * ((466449071 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12791) : ℝ)) (tA 12791 * 163 ^ 2 + 26 / (10 * 12791)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((466449071 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1822813 / 500000000)) ^ 2) * ((1458679003 / 1000000000000000000000000)) + ((4830679037 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12791) : ℝ)) (√(26 / (10 * 12791) : ℝ)) d.D d.V d.P (√(tA 12791) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1822813 / 500000000)) * (((431948641 / 200000000000000)) * ((19096328201 / 500000000000000000))) + ((4830679037 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12791) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((466449071 / 100000000000000000000) : ℝ) + ((4830679037 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12791

namespace BstLean.Part266.Row12791
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12791 163 ∧
    0 ≤ (tableEnvelope C).f1 12791 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12791 163 ∧
    0 ≤ (tableEnvelope C).w1 12791 163 ∧ 0 ≤ (tableEnvelope C).w2 12791 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12791 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12791 163 ∧ 0 ≤ d.f1 12791 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12791 163 ∧ 0 ≤ d.w1 12791 163 ∧ 0 ≤ d.w2 12791 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12791 ≤ 2 * (228 / 100 : ℝ) / 12791 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12791 ≤ 2 * (370 / 100 : ℝ) / 12791 := by
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
    (completeRAData (tableEnvelope C) 12791 163).locationBound 12791 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12791 163).energyBound 12791 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12791 163) (d.f1 12791 163) d.f2 ≤
      32 * (((4501625201 / 1000000000000000000) : ℝ) + (375454561 / 250000000000000000) + (360962541 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12791 163) (d.w1 12791 163)
      (d.w2 12791 163) ≤
      32 * (((897174483 / 50000000000000000000) : ℝ) + (1276644953 / 100000000000000000000) + (466453751 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12791 163) (d.f1 12791 163) d.f2 ≤
      ((4501625201 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4501625201 / 1000000000000000000)) * ((375454561 / 250000000000000000)) * (126 / 100) +
      2 * (((375454561 / 250000000000000000)) ^ 2 + 2 * ((4501625201 / 1000000000000000000)) * ((360962541 / 1000000000000000000))) +
      6 * ((375454561 / 250000000000000000)) * ((360962541 / 1000000000000000000)) * (126 / 100) + 8 * ((360962541 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12791 163) (d.f1 12791 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12791 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12791 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12791 163) (d.f1 12791 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12791 163) (d.w1 12791 163) (d.w2 12791 163)
  have hwexpr0 : 0 ≤ d.w0 12791 163 + d.w1 12791 163 * √(π / 2) +
      2 * d.w2 12791 163 + energyR16 12791 *
      radiusPolynomialRoot16 (d.w0 12791 163) (d.w1 12791 163) (d.w2 12791 163) := by
    positivity
  constructor
  · change (12791 : ℝ) ^ 8 * (mA 12791 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12791 163) (d.f1 12791 163) d.f2 + locationR16 12791 *
        radiusPolynomialRoot16 (d.f0 12791 163) (d.f1 12791 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12791 : ℝ) ^ 8 * (mA 12791 : ℝ) ^ 8 *
        ((((4501625201 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4501625201 / 1000000000000000000)) * ((375454561 / 250000000000000000)) * (126 / 100) +
          2 * (((375454561 / 250000000000000000)) ^ 2 + 2 * ((4501625201 / 1000000000000000000)) * ((360962541 / 1000000000000000000))) +
          6 * ((375454561 / 250000000000000000)) * ((360962541 / 1000000000000000000)) * (126 / 100) + 8 * ((360962541 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12791) *
          (32 * (((4501625201 / 1000000000000000000) : ℝ) + (375454561 / 250000000000000000) + (360962541 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12791 : ℝ) ^ 16 *
      (d.w0 12791 163 + d.w1 12791 163 * √(π / 2) + 2 * d.w2 12791 163 +
        energyR16 12791 * radiusPolynomialRoot16 (d.w0 12791 163) (d.w1 12791 163)
          (d.w2 12791 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12791 : ℝ) ^ 16 *
        (((897174483 / 50000000000000000000) : ℝ) + ((1276644953 / 100000000000000000000)) * (126 / 100) + 2 * ((466453751 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12791) *
          (32 * (((897174483 / 50000000000000000000) : ℝ) + (1276644953 / 100000000000000000000) + (466453751 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12791

/-! A coarse bound on the actual paper statistics constant at dimension 12792. -/
namespace BstLean.Part266.Row12792
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12790 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12790 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12790 128 ≤ (13044 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13044 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12792) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12792 : ℕ))
    (by norm_num : (12792 : ℕ) ≤ 16384)
  have ht : paperTail256 12792 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12792 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12792 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12792 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12792 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12792 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12790 128 * √(2 / (12792 : ℝ)) *
      (√(12792 : ℝ) + paperT0 12792 + paperTail256 12792) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12792 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12792 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12792 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12790 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12790 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12792 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12792

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12792
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12792 (61 / 100) 163 (17 / (100 * 12792)) (26 / (10 * 12792)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12792 (61 / 100) 163 (17 / (100 * 12792)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (233169841 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (364555729 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4827629807 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12792 / 12792 * (61 / 100)) ^ 4 * inverseRadius8 (12792 - 1) /
            envelopeGap 12792 (61 / 100) 163 (17 / (100 * 12792)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12792

namespace BstLean.Part266.Row12792
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12792 163 ≤ (1125185911 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12792 163 ≤ (60060973 / 40000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (360891947 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12792 163 ≤ (1793927799 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12792 163 ≤ (255269077 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12792 163 ≤ (466344359 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (233169841 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (233169841 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (364555729 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4827629807 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((911371 / 250000000) : ℝ) ≤ √(17 / (100 * 12792) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12792) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (431897989 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19093342531 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12792) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12792) ≤ (27638633 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12792) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12792 * (163 : ℝ) ^ 2 + 26 / (10 * 12792) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12792) : ℝ)) (tA 12792 * 163 ^ 2 + 26 / (10 * 12792)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((911371 / 250000000))) * ((233169841 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((911371 / 250000000)) ^ 3) * ((364555729 / 250000000000000000000000))) + ((4827629807 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((911371 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12792) : ℝ)) d.D d.V d.P (√(tA 12792) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((911371 / 250000000)) ^ 2 * (((431897989 / 200000000000000)) * ((19093342531 / 500000000000000000)))) + ((4827629807 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12792) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((911371 / 250000000)) * ((233169841 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12792) : ℝ)) (tA 12792 * 163 ^ 2 + 26 / (10 * 12792)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((233169841 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((911371 / 250000000)) ^ 2) * ((364555729 / 250000000000000000000000)) + ((4827629807 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12792) : ℝ)) (√(26 / (10 * 12792) : ℝ)) d.D d.V d.P (√(tA 12792) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((911371 / 250000000)) * (((431897989 / 200000000000000)) * ((19093342531 / 500000000000000000))) + ((4827629807 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12792) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((233169841 / 50000000000000000000) : ℝ) + ((4827629807 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12792

namespace BstLean.Part266.Row12792
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12792 163 ∧
    0 ≤ (tableEnvelope C).f1 12792 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12792 163 ∧
    0 ≤ (tableEnvelope C).w1 12792 163 ∧ 0 ≤ (tableEnvelope C).w2 12792 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12792 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12792 163 ∧ 0 ≤ d.f1 12792 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12792 163 ∧ 0 ≤ d.w1 12792 163 ∧ 0 ≤ d.w2 12792 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12792 ≤ 2 * (228 / 100 : ℝ) / 12792 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12792 ≤ 2 * (370 / 100 : ℝ) / 12792 := by
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
    (completeRAData (tableEnvelope C) 12792 163).locationBound 12792 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12792 163).energyBound 12792 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12792 163) (d.f1 12792 163) d.f2 ≤
      32 * (((1125185911 / 250000000000000000) : ℝ) + (60060973 / 40000000000000000) + (360891947 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12792 163) (d.w1 12792 163)
      (d.w2 12792 163) ≤
      32 * (((1793927799 / 100000000000000000000) : ℝ) + (255269077 / 20000000000000000000) + (466344359 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12792 163) (d.f1 12792 163) d.f2 ≤
      ((1125185911 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1125185911 / 250000000000000000)) * ((60060973 / 40000000000000000)) * (126 / 100) +
      2 * (((60060973 / 40000000000000000)) ^ 2 + 2 * ((1125185911 / 250000000000000000)) * ((360891947 / 1000000000000000000))) +
      6 * ((60060973 / 40000000000000000)) * ((360891947 / 1000000000000000000)) * (126 / 100) + 8 * ((360891947 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12792 163) (d.f1 12792 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12792 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12792 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12792 163) (d.f1 12792 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12792 163) (d.w1 12792 163) (d.w2 12792 163)
  have hwexpr0 : 0 ≤ d.w0 12792 163 + d.w1 12792 163 * √(π / 2) +
      2 * d.w2 12792 163 + energyR16 12792 *
      radiusPolynomialRoot16 (d.w0 12792 163) (d.w1 12792 163) (d.w2 12792 163) := by
    positivity
  constructor
  · change (12792 : ℝ) ^ 8 * (mA 12792 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12792 163) (d.f1 12792 163) d.f2 + locationR16 12792 *
        radiusPolynomialRoot16 (d.f0 12792 163) (d.f1 12792 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12792 : ℝ) ^ 8 * (mA 12792 : ℝ) ^ 8 *
        ((((1125185911 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1125185911 / 250000000000000000)) * ((60060973 / 40000000000000000)) * (126 / 100) +
          2 * (((60060973 / 40000000000000000)) ^ 2 + 2 * ((1125185911 / 250000000000000000)) * ((360891947 / 1000000000000000000))) +
          6 * ((60060973 / 40000000000000000)) * ((360891947 / 1000000000000000000)) * (126 / 100) + 8 * ((360891947 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12792) *
          (32 * (((1125185911 / 250000000000000000) : ℝ) + (60060973 / 40000000000000000) + (360891947 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12792 : ℝ) ^ 16 *
      (d.w0 12792 163 + d.w1 12792 163 * √(π / 2) + 2 * d.w2 12792 163 +
        energyR16 12792 * radiusPolynomialRoot16 (d.w0 12792 163) (d.w1 12792 163)
          (d.w2 12792 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12792 : ℝ) ^ 16 *
        (((1793927799 / 100000000000000000000) : ℝ) + ((255269077 / 20000000000000000000)) * (126 / 100) + 2 * ((466344359 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12792) *
          (32 * (((1793927799 / 100000000000000000000) : ℝ) + (255269077 / 20000000000000000000) + (466344359 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12792

/-! A coarse bound on the actual paper statistics constant at dimension 12793. -/
namespace BstLean.Part266.Row12793
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12791 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12791 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12791 128 ≤ (13045 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13045 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12793) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12793 : ℕ))
    (by norm_num : (12793 : ℕ) ≤ 16384)
  have ht : paperTail256 12793 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12793 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12793 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12793 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12793 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12793 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12791 128 * √(2 / (12793 : ℝ)) *
      (√(12793 : ℝ) + paperT0 12793 + paperTail256 12793) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12793 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12793 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12793 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12791 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12791 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12793 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12793

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12793
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12793 (61 / 100) 163 (17 / (100 * 12793)) (26 / (10 * 12793)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12793 (61 / 100) 163 (17 / (100 * 12793)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (466230327 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (45555219 / 31250000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (603072843 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12793 / 12793 * (61 / 100)) ^ 4 * inverseRadius8 (12793 - 1) /
            envelopeGap 12793 (61 / 100) 163 (17 / (100 * 12793)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12793

namespace BstLean.Part266.Row12793
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12793 163 ≤ (4499865953 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12793 163 ≤ (375307831 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (360821473 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12793 163 ≤ (896753753 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12793 163 ≤ (319011567 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12793 163 ≤ (466235001 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (466230327 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (466230327 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (45555219 / 31250000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (603072843 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3645341 / 1000000000) : ℝ) ≤ √(17 / (100 * 12793) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12793) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1079618367 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38180715133 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12793) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12793) ≤ (11054589 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12793) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12793 * (163 : ℝ) ^ 2 + 26 / (10 * 12793) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12793) : ℝ)) (tA 12793 * 163 ^ 2 + 26 / (10 * 12793)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3645341 / 1000000000))) * ((466230327 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3645341 / 1000000000)) ^ 3) * ((45555219 / 31250000000000000000000))) + ((603072843 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3645341 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12793) : ℝ)) d.D d.V d.P (√(tA 12793) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3645341 / 1000000000)) ^ 2 * (((1079618367 / 500000000000000)) * ((38180715133 / 1000000000000000000)))) + ((603072843 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12793) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3645341 / 1000000000)) * ((466230327 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12793) : ℝ)) (tA 12793 * 163 ^ 2 + 26 / (10 * 12793)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((466230327 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3645341 / 1000000000)) ^ 2) * ((45555219 / 31250000000000000000000)) + ((603072843 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12793) : ℝ)) (√(26 / (10 * 12793) : ℝ)) d.D d.V d.P (√(tA 12793) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3645341 / 1000000000)) * (((1079618367 / 500000000000000)) * ((38180715133 / 1000000000000000000))) + ((603072843 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12793) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((466230327 / 100000000000000000000) : ℝ) + ((603072843 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12793

namespace BstLean.Part266.Row12793
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12793 163 ∧
    0 ≤ (tableEnvelope C).f1 12793 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12793 163 ∧
    0 ≤ (tableEnvelope C).w1 12793 163 ∧ 0 ≤ (tableEnvelope C).w2 12793 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12793 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12793 163 ∧ 0 ≤ d.f1 12793 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12793 163 ∧ 0 ≤ d.w1 12793 163 ∧ 0 ≤ d.w2 12793 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12793 ≤ 2 * (228 / 100 : ℝ) / 12793 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12793 ≤ 2 * (370 / 100 : ℝ) / 12793 := by
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
    (completeRAData (tableEnvelope C) 12793 163).locationBound 12793 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12793 163).energyBound 12793 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12793 163) (d.f1 12793 163) d.f2 ≤
      32 * (((4499865953 / 1000000000000000000) : ℝ) + (375307831 / 250000000000000000) + (360821473 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12793 163) (d.w1 12793 163)
      (d.w2 12793 163) ≤
      32 * (((896753753 / 50000000000000000000) : ℝ) + (319011567 / 25000000000000000000) + (466235001 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12793 163) (d.f1 12793 163) d.f2 ≤
      ((4499865953 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4499865953 / 1000000000000000000)) * ((375307831 / 250000000000000000)) * (126 / 100) +
      2 * (((375307831 / 250000000000000000)) ^ 2 + 2 * ((4499865953 / 1000000000000000000)) * ((360821473 / 1000000000000000000))) +
      6 * ((375307831 / 250000000000000000)) * ((360821473 / 1000000000000000000)) * (126 / 100) + 8 * ((360821473 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12793 163) (d.f1 12793 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12793 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12793 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12793 163) (d.f1 12793 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12793 163) (d.w1 12793 163) (d.w2 12793 163)
  have hwexpr0 : 0 ≤ d.w0 12793 163 + d.w1 12793 163 * √(π / 2) +
      2 * d.w2 12793 163 + energyR16 12793 *
      radiusPolynomialRoot16 (d.w0 12793 163) (d.w1 12793 163) (d.w2 12793 163) := by
    positivity
  constructor
  · change (12793 : ℝ) ^ 8 * (mA 12793 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12793 163) (d.f1 12793 163) d.f2 + locationR16 12793 *
        radiusPolynomialRoot16 (d.f0 12793 163) (d.f1 12793 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12793 : ℝ) ^ 8 * (mA 12793 : ℝ) ^ 8 *
        ((((4499865953 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4499865953 / 1000000000000000000)) * ((375307831 / 250000000000000000)) * (126 / 100) +
          2 * (((375307831 / 250000000000000000)) ^ 2 + 2 * ((4499865953 / 1000000000000000000)) * ((360821473 / 1000000000000000000))) +
          6 * ((375307831 / 250000000000000000)) * ((360821473 / 1000000000000000000)) * (126 / 100) + 8 * ((360821473 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12793) *
          (32 * (((4499865953 / 1000000000000000000) : ℝ) + (375307831 / 250000000000000000) + (360821473 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12793 : ℝ) ^ 16 *
      (d.w0 12793 163 + d.w1 12793 163 * √(π / 2) + 2 * d.w2 12793 163 +
        energyR16 12793 * radiusPolynomialRoot16 (d.w0 12793 163) (d.w1 12793 163)
          (d.w2 12793 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12793 : ℝ) ^ 16 *
        (((896753753 / 50000000000000000000) : ℝ) + ((319011567 / 25000000000000000000)) * (126 / 100) + 2 * ((466235001 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12793) *
          (32 * (((896753753 / 50000000000000000000) : ℝ) + (319011567 / 25000000000000000000) + (466235001 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12793

/-! A coarse bound on the actual paper statistics constant at dimension 12794. -/
namespace BstLean.Part266.Row12794
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12792 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12792 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12792 128 ≤ (13046 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13046 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12794) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12794 : ℕ))
    (by norm_num : (12794 : ℕ) ≤ 16384)
  have ht : paperTail256 12794 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12794 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12794 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12794 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12794 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12794 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12792 128 * √(2 / (12794 : ℝ)) *
      (√(12794 : ℝ) + paperT0 12794 + paperTail256 12794) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12794 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12794 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12794 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12792 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12792 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12794 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12794

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12794
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12794 (61 / 100) 163 (17 / (100 * 12794)) (26 / (10 * 12794)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12794 (61 / 100) 163 (17 / (100 * 12794)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (233060503 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (728655639 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4821537847 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12794 / 12794 * (61 / 100)) ^ 4 * inverseRadius8 (12794 - 1) /
            envelopeGap 12794 (61 / 100) 163 (17 / (100 * 12794)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12794

namespace BstLean.Part266.Row12794
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12794 163 ≤ (4498984999 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12794 163 ≤ (1500937593 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (360750921 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12794 163 ≤ (1793086627 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12794 163 ≤ (1275746899 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12794 163 ≤ (466125677 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (233060503 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (233060503 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (728655639 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4821537847 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3645199 / 1000000000) : ℝ) ≤ √(17 / (100 * 12794) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12794) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (539745893 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (38174746601 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12794) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12794) ≤ (110537249 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12794) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12794 * (163 : ℝ) ^ 2 + 26 / (10 * 12794) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12794) : ℝ)) (tA 12794 * 163 ^ 2 + 26 / (10 * 12794)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3645199 / 1000000000))) * ((233060503 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3645199 / 1000000000)) ^ 3) * ((728655639 / 500000000000000000000000))) + ((4821537847 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3645199 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12794) : ℝ)) d.D d.V d.P (√(tA 12794) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3645199 / 1000000000)) ^ 2 * (((539745893 / 250000000000000)) * ((38174746601 / 1000000000000000000)))) + ((4821537847 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12794) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3645199 / 1000000000)) * ((233060503 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12794) : ℝ)) (tA 12794 * 163 ^ 2 + 26 / (10 * 12794)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((233060503 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3645199 / 1000000000)) ^ 2) * ((728655639 / 500000000000000000000000)) + ((4821537847 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12794) : ℝ)) (√(26 / (10 * 12794) : ℝ)) d.D d.V d.P (√(tA 12794) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3645199 / 1000000000)) * (((539745893 / 250000000000000)) * ((38174746601 / 1000000000000000000))) + ((4821537847 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12794) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((233060503 / 50000000000000000000) : ℝ) + ((4821537847 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12794

namespace BstLean.Part266.Row12794
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12794 163 ∧
    0 ≤ (tableEnvelope C).f1 12794 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12794 163 ∧
    0 ≤ (tableEnvelope C).w1 12794 163 ∧ 0 ≤ (tableEnvelope C).w2 12794 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12794 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12794 163 ∧ 0 ≤ d.f1 12794 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12794 163 ∧ 0 ≤ d.w1 12794 163 ∧ 0 ≤ d.w2 12794 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12794 ≤ 2 * (228 / 100 : ℝ) / 12794 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12794 ≤ 2 * (370 / 100 : ℝ) / 12794 := by
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
    (completeRAData (tableEnvelope C) 12794 163).locationBound 12794 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12794 163).energyBound 12794 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12794 163) (d.f1 12794 163) d.f2 ≤
      32 * (((4498984999 / 1000000000000000000) : ℝ) + (1500937593 / 1000000000000000000) + (360750921 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12794 163) (d.w1 12794 163)
      (d.w2 12794 163) ≤
      32 * (((1793086627 / 100000000000000000000) : ℝ) + (1275746899 / 100000000000000000000) + (466125677 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12794 163) (d.f1 12794 163) d.f2 ≤
      ((4498984999 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4498984999 / 1000000000000000000)) * ((1500937593 / 1000000000000000000)) * (126 / 100) +
      2 * (((1500937593 / 1000000000000000000)) ^ 2 + 2 * ((4498984999 / 1000000000000000000)) * ((360750921 / 1000000000000000000))) +
      6 * ((1500937593 / 1000000000000000000)) * ((360750921 / 1000000000000000000)) * (126 / 100) + 8 * ((360750921 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12794 163) (d.f1 12794 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12794 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12794 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12794 163) (d.f1 12794 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12794 163) (d.w1 12794 163) (d.w2 12794 163)
  have hwexpr0 : 0 ≤ d.w0 12794 163 + d.w1 12794 163 * √(π / 2) +
      2 * d.w2 12794 163 + energyR16 12794 *
      radiusPolynomialRoot16 (d.w0 12794 163) (d.w1 12794 163) (d.w2 12794 163) := by
    positivity
  constructor
  · change (12794 : ℝ) ^ 8 * (mA 12794 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12794 163) (d.f1 12794 163) d.f2 + locationR16 12794 *
        radiusPolynomialRoot16 (d.f0 12794 163) (d.f1 12794 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12794 : ℝ) ^ 8 * (mA 12794 : ℝ) ^ 8 *
        ((((4498984999 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4498984999 / 1000000000000000000)) * ((1500937593 / 1000000000000000000)) * (126 / 100) +
          2 * (((1500937593 / 1000000000000000000)) ^ 2 + 2 * ((4498984999 / 1000000000000000000)) * ((360750921 / 1000000000000000000))) +
          6 * ((1500937593 / 1000000000000000000)) * ((360750921 / 1000000000000000000)) * (126 / 100) + 8 * ((360750921 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12794) *
          (32 * (((4498984999 / 1000000000000000000) : ℝ) + (1500937593 / 1000000000000000000) + (360750921 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12794 : ℝ) ^ 16 *
      (d.w0 12794 163 + d.w1 12794 163 * √(π / 2) + 2 * d.w2 12794 163 +
        energyR16 12794 * radiusPolynomialRoot16 (d.w0 12794 163) (d.w1 12794 163)
          (d.w2 12794 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12794 : ℝ) ^ 16 *
        (((1793086627 / 100000000000000000000) : ℝ) + ((1275746899 / 100000000000000000000)) * (126 / 100) + 2 * ((466125677 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12794) *
          (32 * (((1793086627 / 100000000000000000000) : ℝ) + (1275746899 / 100000000000000000000) + (466125677 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12794

/-! A coarse bound on the actual paper statistics constant at dimension 12795. -/
namespace BstLean.Part266.Row12795
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12793 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12793 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12793 128 ≤ (13047 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13047 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12795) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12795 : ℕ))
    (by norm_num : (12795 : ℕ) ≤ 16384)
  have ht : paperTail256 12795 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12795 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12795 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12795 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12795 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12795 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12793 128 * √(2 / (12795 : ℝ)) *
      (√(12795 : ℝ) + paperT0 12795 + paperTail256 12795) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12795 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12795 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12795 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12793 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12793 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12795 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12795

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12795
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12795 (61 / 100) 163 (17 / (100 * 12795)) (26 / (10 * 12795)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12795 (61 / 100) 163 (17 / (100 * 12795)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (466011719 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (58274229 / 40000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4818495113 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12795 / 12795 * (61 / 100)) ^ 4 * inverseRadius8 (12795 - 1) /
            envelopeGap 12795 (61 / 100) 163 (17 / (100 * 12795)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12795

namespace BstLean.Part266.Row12795
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12795 163 ≤ (8785367 / 1953125000000000)
  f1 : (tableEnvelope C).f1 12795 163 ≤ (1500644777 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (45085061 / 125000000000000000)
  w0 : (tableEnvelope C).w0 12795 163 ≤ (1792666619 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12795 163 ≤ (637723989 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12795 163 ≤ (466016387 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (466011719 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (466011719 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (58274229 / 40000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4818495113 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((28477 / 7812500) : ℝ) ≤ √(17 / (100 * 12795) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12795) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1079365229 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19084389727 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12795) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12795) ≤ (11052861 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12795) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12795 * (163 : ℝ) ^ 2 + 26 / (10 * 12795) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12795) : ℝ)) (tA 12795 * 163 ^ 2 + 26 / (10 * 12795)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((28477 / 7812500))) * ((466011719 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((28477 / 7812500)) ^ 3) * ((58274229 / 40000000000000000000000))) + ((4818495113 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((28477 / 7812500)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12795) : ℝ)) d.D d.V d.P (√(tA 12795) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((28477 / 7812500)) ^ 2 * (((1079365229 / 500000000000000)) * ((19084389727 / 500000000000000000)))) + ((4818495113 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12795) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((28477 / 7812500)) * ((466011719 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12795) : ℝ)) (tA 12795 * 163 ^ 2 + 26 / (10 * 12795)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((466011719 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((28477 / 7812500)) ^ 2) * ((58274229 / 40000000000000000000000)) + ((4818495113 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12795) : ℝ)) (√(26 / (10 * 12795) : ℝ)) d.D d.V d.P (√(tA 12795) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((28477 / 7812500)) * (((1079365229 / 500000000000000)) * ((19084389727 / 500000000000000000))) + ((4818495113 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12795) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((466011719 / 100000000000000000000) : ℝ) + ((4818495113 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12795

namespace BstLean.Part266.Row12795
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12795 163 ∧
    0 ≤ (tableEnvelope C).f1 12795 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12795 163 ∧
    0 ≤ (tableEnvelope C).w1 12795 163 ∧ 0 ≤ (tableEnvelope C).w2 12795 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12795 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12795 163 ∧ 0 ≤ d.f1 12795 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12795 163 ∧ 0 ≤ d.w1 12795 163 ∧ 0 ≤ d.w2 12795 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12795 ≤ 2 * (228 / 100 : ℝ) / 12795 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12795 ≤ 2 * (370 / 100 : ℝ) / 12795 := by
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
    (completeRAData (tableEnvelope C) 12795 163).locationBound 12795 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12795 163).energyBound 12795 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12795 163) (d.f1 12795 163) d.f2 ≤
      32 * (((8785367 / 1953125000000000) : ℝ) + (1500644777 / 1000000000000000000) + (45085061 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12795 163) (d.w1 12795 163)
      (d.w2 12795 163) ≤
      32 * (((1792666619 / 100000000000000000000) : ℝ) + (637723989 / 50000000000000000000) + (466016387 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12795 163) (d.f1 12795 163) d.f2 ≤
      ((8785367 / 1953125000000000) : ℝ) ^ 2 + 2 * ((8785367 / 1953125000000000)) * ((1500644777 / 1000000000000000000)) * (126 / 100) +
      2 * (((1500644777 / 1000000000000000000)) ^ 2 + 2 * ((8785367 / 1953125000000000)) * ((45085061 / 125000000000000000))) +
      6 * ((1500644777 / 1000000000000000000)) * ((45085061 / 125000000000000000)) * (126 / 100) + 8 * ((45085061 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12795 163) (d.f1 12795 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12795 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12795 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12795 163) (d.f1 12795 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12795 163) (d.w1 12795 163) (d.w2 12795 163)
  have hwexpr0 : 0 ≤ d.w0 12795 163 + d.w1 12795 163 * √(π / 2) +
      2 * d.w2 12795 163 + energyR16 12795 *
      radiusPolynomialRoot16 (d.w0 12795 163) (d.w1 12795 163) (d.w2 12795 163) := by
    positivity
  constructor
  · change (12795 : ℝ) ^ 8 * (mA 12795 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12795 163) (d.f1 12795 163) d.f2 + locationR16 12795 *
        radiusPolynomialRoot16 (d.f0 12795 163) (d.f1 12795 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12795 : ℝ) ^ 8 * (mA 12795 : ℝ) ^ 8 *
        ((((8785367 / 1953125000000000) : ℝ) ^ 2 + 2 * ((8785367 / 1953125000000000)) * ((1500644777 / 1000000000000000000)) * (126 / 100) +
          2 * (((1500644777 / 1000000000000000000)) ^ 2 + 2 * ((8785367 / 1953125000000000)) * ((45085061 / 125000000000000000))) +
          6 * ((1500644777 / 1000000000000000000)) * ((45085061 / 125000000000000000)) * (126 / 100) + 8 * ((45085061 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12795) *
          (32 * (((8785367 / 1953125000000000) : ℝ) + (1500644777 / 1000000000000000000) + (45085061 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12795 : ℝ) ^ 16 *
      (d.w0 12795 163 + d.w1 12795 163 * √(π / 2) + 2 * d.w2 12795 163 +
        energyR16 12795 * radiusPolynomialRoot16 (d.w0 12795 163) (d.w1 12795 163)
          (d.w2 12795 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12795 : ℝ) ^ 16 *
        (((1792666619 / 100000000000000000000) : ℝ) + ((637723989 / 50000000000000000000)) * (126 / 100) + 2 * ((466016387 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12795) *
          (32 * (((1792666619 / 100000000000000000000) : ℝ) + (637723989 / 50000000000000000000) + (466016387 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12795

/-! A coarse bound on the actual paper statistics constant at dimension 12796. -/
namespace BstLean.Part266.Row12796
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12794 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12794 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12794 128 ≤ (13048 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13048 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12796) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12796 : ℕ))
    (by norm_num : (12796 : ℕ) ≤ 16384)
  have ht : paperTail256 12796 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12796 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12796 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12796 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12796 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12796 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12794 128 * √(2 / (12796 : ℝ)) *
      (√(12796 : ℝ) + paperT0 12796 + paperTail256 12796) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12796 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12796 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12796 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12794 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12794 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12796 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12796

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12796
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12796 (61 / 100) 163 (17 / (100 * 12796)) (26 / (10 * 12796)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12796 (61 / 100) 163 (17 / (100 * 12796)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (232951233 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1456400351 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2407727271 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12796 / 12796 * (61 / 100)) ^ 4 * inverseRadius8 (12796 - 1) /
            envelopeGap 12796 (61 / 100) 163 (17 / (100 * 12796)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12796

namespace BstLean.Part266.Row12796
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12796 163 ≤ (89944551 / 20000000000000000)
  f1 : (tableEnvelope C).f1 12796 163 ≤ (1500351233 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (180304989 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12796 163 ≤ (1792246027 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12796 163 ≤ (159393601 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 12796 163 ≤ (465907131 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (232951233 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (232951233 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1456400351 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2407727271 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1822457 / 500000000) : ℝ) ≤ √(17 / (100 * 12796) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12796) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1079238697 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (954070343 / 25000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12796) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12796) ≤ (110519973 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12796) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12796 * (163 : ℝ) ^ 2 + 26 / (10 * 12796) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12796) : ℝ)) (tA 12796 * 163 ^ 2 + 26 / (10 * 12796)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1822457 / 500000000))) * ((232951233 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1822457 / 500000000)) ^ 3) * ((1456400351 / 1000000000000000000000000))) + ((2407727271 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1822457 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12796) : ℝ)) d.D d.V d.P (√(tA 12796) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1822457 / 500000000)) ^ 2 * (((1079238697 / 500000000000000)) * ((954070343 / 25000000000000000)))) + ((2407727271 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12796) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1822457 / 500000000)) * ((232951233 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12796) : ℝ)) (tA 12796 * 163 ^ 2 + 26 / (10 * 12796)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((232951233 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1822457 / 500000000)) ^ 2) * ((1456400351 / 1000000000000000000000000)) + ((2407727271 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12796) : ℝ)) (√(26 / (10 * 12796) : ℝ)) d.D d.V d.P (√(tA 12796) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1822457 / 500000000)) * (((1079238697 / 500000000000000)) * ((954070343 / 25000000000000000))) + ((2407727271 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12796) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((232951233 / 50000000000000000000) : ℝ) + ((2407727271 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12796

namespace BstLean.Part266.Row12796
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12796 163 ∧
    0 ≤ (tableEnvelope C).f1 12796 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12796 163 ∧
    0 ≤ (tableEnvelope C).w1 12796 163 ∧ 0 ≤ (tableEnvelope C).w2 12796 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12796 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12796 163 ∧ 0 ≤ d.f1 12796 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12796 163 ∧ 0 ≤ d.w1 12796 163 ∧ 0 ≤ d.w2 12796 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12796 ≤ 2 * (228 / 100 : ℝ) / 12796 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12796 ≤ 2 * (370 / 100 : ℝ) / 12796 := by
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
    (completeRAData (tableEnvelope C) 12796 163).locationBound 12796 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12796 163).energyBound 12796 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12796 163) (d.f1 12796 163) d.f2 ≤
      32 * (((89944551 / 20000000000000000) : ℝ) + (1500351233 / 1000000000000000000) + (180304989 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12796 163) (d.w1 12796 163)
      (d.w2 12796 163) ≤
      32 * (((1792246027 / 100000000000000000000) : ℝ) + (159393601 / 12500000000000000000) + (465907131 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12796 163) (d.f1 12796 163) d.f2 ≤
      ((89944551 / 20000000000000000) : ℝ) ^ 2 + 2 * ((89944551 / 20000000000000000)) * ((1500351233 / 1000000000000000000)) * (126 / 100) +
      2 * (((1500351233 / 1000000000000000000)) ^ 2 + 2 * ((89944551 / 20000000000000000)) * ((180304989 / 500000000000000000))) +
      6 * ((1500351233 / 1000000000000000000)) * ((180304989 / 500000000000000000)) * (126 / 100) + 8 * ((180304989 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12796 163) (d.f1 12796 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12796 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12796 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12796 163) (d.f1 12796 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12796 163) (d.w1 12796 163) (d.w2 12796 163)
  have hwexpr0 : 0 ≤ d.w0 12796 163 + d.w1 12796 163 * √(π / 2) +
      2 * d.w2 12796 163 + energyR16 12796 *
      radiusPolynomialRoot16 (d.w0 12796 163) (d.w1 12796 163) (d.w2 12796 163) := by
    positivity
  constructor
  · change (12796 : ℝ) ^ 8 * (mA 12796 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12796 163) (d.f1 12796 163) d.f2 + locationR16 12796 *
        radiusPolynomialRoot16 (d.f0 12796 163) (d.f1 12796 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12796 : ℝ) ^ 8 * (mA 12796 : ℝ) ^ 8 *
        ((((89944551 / 20000000000000000) : ℝ) ^ 2 + 2 * ((89944551 / 20000000000000000)) * ((1500351233 / 1000000000000000000)) * (126 / 100) +
          2 * (((1500351233 / 1000000000000000000)) ^ 2 + 2 * ((89944551 / 20000000000000000)) * ((180304989 / 500000000000000000))) +
          6 * ((1500351233 / 1000000000000000000)) * ((180304989 / 500000000000000000)) * (126 / 100) + 8 * ((180304989 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12796) *
          (32 * (((89944551 / 20000000000000000) : ℝ) + (1500351233 / 1000000000000000000) + (180304989 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12796 : ℝ) ^ 16 *
      (d.w0 12796 163 + d.w1 12796 163 * √(π / 2) + 2 * d.w2 12796 163 +
        energyR16 12796 * radiusPolynomialRoot16 (d.w0 12796 163) (d.w1 12796 163)
          (d.w2 12796 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12796 : ℝ) ^ 16 *
        (((1792246027 / 100000000000000000000) : ℝ) + ((159393601 / 12500000000000000000)) * (126 / 100) + 2 * ((465907131 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12796) *
          (32 * (((1792246027 / 100000000000000000000) : ℝ) + (159393601 / 12500000000000000000) + (465907131 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12796

/-! A coarse bound on the actual paper statistics constant at dimension 12797. -/
namespace BstLean.Part266.Row12797
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12795 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12795 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12795 128 ≤ (13049 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13049 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12797) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12797 : ℕ))
    (by norm_num : (12797 : ℕ) ≤ 16384)
  have ht : paperTail256 12797 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12797 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12797 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12797 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12797 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12797 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12795 128 * √(2 / (12797 : ℝ)) *
      (√(12797 : ℝ) + paperT0 12797 + paperTail256 12797) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12797 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12797 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12797 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12795 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12795 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12797 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12797

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12797
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12797 (61 / 100) 163 (17 / (100 * 12797)) (26 / (10 * 12797)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12797 (61 / 100) 163 (17 / (100 * 12797)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (465793247 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (291189031 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4812416131 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12797 / 12797 * (61 / 100)) ^ 4 * inverseRadius8 (12797 - 1) /
            envelopeGap 12797 (61 / 100) 163 (17 / (100 * 12797)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12797

namespace BstLean.Part266.Row12797
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12797 163 ≤ (562043437 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12797 163 ≤ (1500057783 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (11266859 / 31250000000000000)
  w0 : (tableEnvelope C).w0 12797 163 ≤ (1791825579 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12797 163 ≤ (159356217 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 12797 163 ≤ (465797909 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (465793247 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (465793247 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (291189031 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4812416131 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((911193 / 250000000) : ℝ) ≤ √(17 / (100 * 12797) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12797) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2158224379 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (19078424693 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12797) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12797) ≤ (13813917 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12797) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12797 * (163 : ℝ) ^ 2 + 26 / (10 * 12797) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12797) : ℝ)) (tA 12797 * 163 ^ 2 + 26 / (10 * 12797)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((911193 / 250000000))) * ((465793247 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((911193 / 250000000)) ^ 3) * ((291189031 / 200000000000000000000000))) + ((4812416131 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((911193 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12797) : ℝ)) d.D d.V d.P (√(tA 12797) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((911193 / 250000000)) ^ 2 * (((2158224379 / 1000000000000000)) * ((19078424693 / 500000000000000000)))) + ((4812416131 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12797) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((911193 / 250000000)) * ((465793247 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12797) : ℝ)) (tA 12797 * 163 ^ 2 + 26 / (10 * 12797)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((465793247 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((911193 / 250000000)) ^ 2) * ((291189031 / 200000000000000000000000)) + ((4812416131 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12797) : ℝ)) (√(26 / (10 * 12797) : ℝ)) d.D d.V d.P (√(tA 12797) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((911193 / 250000000)) * (((2158224379 / 1000000000000000)) * ((19078424693 / 500000000000000000))) + ((4812416131 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12797) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((465793247 / 100000000000000000000) : ℝ) + ((4812416131 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12797

namespace BstLean.Part266.Row12797
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12797 163 ∧
    0 ≤ (tableEnvelope C).f1 12797 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12797 163 ∧
    0 ≤ (tableEnvelope C).w1 12797 163 ∧ 0 ≤ (tableEnvelope C).w2 12797 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12797 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12797 163 ∧ 0 ≤ d.f1 12797 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12797 163 ∧ 0 ≤ d.w1 12797 163 ∧ 0 ≤ d.w2 12797 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12797 ≤ 2 * (228 / 100 : ℝ) / 12797 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12797 ≤ 2 * (370 / 100 : ℝ) / 12797 := by
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
    (completeRAData (tableEnvelope C) 12797 163).locationBound 12797 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12797 163).energyBound 12797 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12797 163) (d.f1 12797 163) d.f2 ≤
      32 * (((562043437 / 125000000000000000) : ℝ) + (1500057783 / 1000000000000000000) + (11266859 / 31250000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12797 163) (d.w1 12797 163)
      (d.w2 12797 163) ≤
      32 * (((1791825579 / 100000000000000000000) : ℝ) + (159356217 / 12500000000000000000) + (465797909 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12797 163) (d.f1 12797 163) d.f2 ≤
      ((562043437 / 125000000000000000) : ℝ) ^ 2 + 2 * ((562043437 / 125000000000000000)) * ((1500057783 / 1000000000000000000)) * (126 / 100) +
      2 * (((1500057783 / 1000000000000000000)) ^ 2 + 2 * ((562043437 / 125000000000000000)) * ((11266859 / 31250000000000000))) +
      6 * ((1500057783 / 1000000000000000000)) * ((11266859 / 31250000000000000)) * (126 / 100) + 8 * ((11266859 / 31250000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12797 163) (d.f1 12797 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12797 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12797 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12797 163) (d.f1 12797 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12797 163) (d.w1 12797 163) (d.w2 12797 163)
  have hwexpr0 : 0 ≤ d.w0 12797 163 + d.w1 12797 163 * √(π / 2) +
      2 * d.w2 12797 163 + energyR16 12797 *
      radiusPolynomialRoot16 (d.w0 12797 163) (d.w1 12797 163) (d.w2 12797 163) := by
    positivity
  constructor
  · change (12797 : ℝ) ^ 8 * (mA 12797 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12797 163) (d.f1 12797 163) d.f2 + locationR16 12797 *
        radiusPolynomialRoot16 (d.f0 12797 163) (d.f1 12797 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12797 : ℝ) ^ 8 * (mA 12797 : ℝ) ^ 8 *
        ((((562043437 / 125000000000000000) : ℝ) ^ 2 + 2 * ((562043437 / 125000000000000000)) * ((1500057783 / 1000000000000000000)) * (126 / 100) +
          2 * (((1500057783 / 1000000000000000000)) ^ 2 + 2 * ((562043437 / 125000000000000000)) * ((11266859 / 31250000000000000))) +
          6 * ((1500057783 / 1000000000000000000)) * ((11266859 / 31250000000000000)) * (126 / 100) + 8 * ((11266859 / 31250000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12797) *
          (32 * (((562043437 / 125000000000000000) : ℝ) + (1500057783 / 1000000000000000000) + (11266859 / 31250000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12797 : ℝ) ^ 16 *
      (d.w0 12797 163 + d.w1 12797 163 * √(π / 2) + 2 * d.w2 12797 163 +
        energyR16 12797 * radiusPolynomialRoot16 (d.w0 12797 163) (d.w1 12797 163)
          (d.w2 12797 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12797 : ℝ) ^ 16 *
        (((1791825579 / 100000000000000000000) : ℝ) + ((159356217 / 12500000000000000000)) * (126 / 100) + 2 * ((465797909 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12797) *
          (32 * (((1791825579 / 100000000000000000000) : ℝ) + (159356217 / 12500000000000000000) + (465797909 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12797

/-! A coarse bound on the actual paper statistics constant at dimension 12798. -/
namespace BstLean.Part266.Row12798
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12796 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12796 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12796 128 ≤ (13050 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13050 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12798) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12798 : ℕ))
    (by norm_num : (12798 : ℕ) ≤ 16384)
  have ht : paperTail256 12798 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12798 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12798 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12798 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12798 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12798 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12796 128 * √(2 / (12798 : ℝ)) *
      (√(12798 : ℝ) + paperT0 12798 + paperTail256 12798) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12798 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12798 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12798 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12796 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12796 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12798 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12798

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12798
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12798 (61 / 100) 163 (17 / (100 * 12798)) (26 / (10 * 12798)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12798 (61 / 100) 163 (17 / (100 * 12798)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (465684063 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1455490137 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (120234497 / 25000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12798 / 12798 * (61 / 100)) ^ 4 * inverseRadius8 (12798 - 1) /
            envelopeGap 12798 (61 / 100) 163 (17 / (100 * 12798)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12798

namespace BstLean.Part266.Row12798
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12798 163 ≤ (561933913 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12798 163 ≤ (374941313 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (360469119 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12798 163 ≤ (1791406003 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12798 163 ≤ (318637779 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12798 163 ≤ (232844361 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (465684063 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (465684063 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1455490137 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (120234497 / 25000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3644629 / 1000000000) : ℝ) ≤ √(17 / (100 * 12798) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12798) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (269746427 / 125000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9537721613 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12798) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12798) ≤ (110502701 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12798) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12798 * (163 : ℝ) ^ 2 + 26 / (10 * 12798) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12798) : ℝ)) (tA 12798 * 163 ^ 2 + 26 / (10 * 12798)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3644629 / 1000000000))) * ((465684063 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3644629 / 1000000000)) ^ 3) * ((1455490137 / 1000000000000000000000000))) + ((120234497 / 25000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3644629 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12798) : ℝ)) d.D d.V d.P (√(tA 12798) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3644629 / 1000000000)) ^ 2 * (((269746427 / 125000000000000)) * ((9537721613 / 250000000000000000)))) + ((120234497 / 25000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12798) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3644629 / 1000000000)) * ((465684063 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12798) : ℝ)) (tA 12798 * 163 ^ 2 + 26 / (10 * 12798)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((465684063 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3644629 / 1000000000)) ^ 2) * ((1455490137 / 1000000000000000000000000)) + ((120234497 / 25000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12798) : ℝ)) (√(26 / (10 * 12798) : ℝ)) d.D d.V d.P (√(tA 12798) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3644629 / 1000000000)) * (((269746427 / 125000000000000)) * ((9537721613 / 250000000000000000))) + ((120234497 / 25000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12798) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((465684063 / 100000000000000000000) : ℝ) + ((120234497 / 25000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12798

namespace BstLean.Part266.Row12798
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12798 163 ∧
    0 ≤ (tableEnvelope C).f1 12798 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12798 163 ∧
    0 ≤ (tableEnvelope C).w1 12798 163 ∧ 0 ≤ (tableEnvelope C).w2 12798 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12798 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12798 163 ∧ 0 ≤ d.f1 12798 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12798 163 ∧ 0 ≤ d.w1 12798 163 ∧ 0 ≤ d.w2 12798 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12798 ≤ 2 * (228 / 100 : ℝ) / 12798 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12798 ≤ 2 * (370 / 100 : ℝ) / 12798 := by
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
    (completeRAData (tableEnvelope C) 12798 163).locationBound 12798 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12798 163).energyBound 12798 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12798 163) (d.f1 12798 163) d.f2 ≤
      32 * (((561933913 / 125000000000000000) : ℝ) + (374941313 / 250000000000000000) + (360469119 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12798 163) (d.w1 12798 163)
      (d.w2 12798 163) ≤
      32 * (((1791406003 / 100000000000000000000) : ℝ) + (318637779 / 25000000000000000000) + (232844361 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12798 163) (d.f1 12798 163) d.f2 ≤
      ((561933913 / 125000000000000000) : ℝ) ^ 2 + 2 * ((561933913 / 125000000000000000)) * ((374941313 / 250000000000000000)) * (126 / 100) +
      2 * (((374941313 / 250000000000000000)) ^ 2 + 2 * ((561933913 / 125000000000000000)) * ((360469119 / 1000000000000000000))) +
      6 * ((374941313 / 250000000000000000)) * ((360469119 / 1000000000000000000)) * (126 / 100) + 8 * ((360469119 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12798 163) (d.f1 12798 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12798 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12798 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12798 163) (d.f1 12798 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12798 163) (d.w1 12798 163) (d.w2 12798 163)
  have hwexpr0 : 0 ≤ d.w0 12798 163 + d.w1 12798 163 * √(π / 2) +
      2 * d.w2 12798 163 + energyR16 12798 *
      radiusPolynomialRoot16 (d.w0 12798 163) (d.w1 12798 163) (d.w2 12798 163) := by
    positivity
  constructor
  · change (12798 : ℝ) ^ 8 * (mA 12798 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12798 163) (d.f1 12798 163) d.f2 + locationR16 12798 *
        radiusPolynomialRoot16 (d.f0 12798 163) (d.f1 12798 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12798 : ℝ) ^ 8 * (mA 12798 : ℝ) ^ 8 *
        ((((561933913 / 125000000000000000) : ℝ) ^ 2 + 2 * ((561933913 / 125000000000000000)) * ((374941313 / 250000000000000000)) * (126 / 100) +
          2 * (((374941313 / 250000000000000000)) ^ 2 + 2 * ((561933913 / 125000000000000000)) * ((360469119 / 1000000000000000000))) +
          6 * ((374941313 / 250000000000000000)) * ((360469119 / 1000000000000000000)) * (126 / 100) + 8 * ((360469119 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12798) *
          (32 * (((561933913 / 125000000000000000) : ℝ) + (374941313 / 250000000000000000) + (360469119 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12798 : ℝ) ^ 16 *
      (d.w0 12798 163 + d.w1 12798 163 * √(π / 2) + 2 * d.w2 12798 163 +
        energyR16 12798 * radiusPolynomialRoot16 (d.w0 12798 163) (d.w1 12798 163)
          (d.w2 12798 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12798 : ℝ) ^ 16 *
        (((1791406003 / 100000000000000000000) : ℝ) + ((318637779 / 25000000000000000000)) * (126 / 100) + 2 * ((232844361 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12798) *
          (32 * (((1791406003 / 100000000000000000000) : ℝ) + (318637779 / 25000000000000000000) + (232844361 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12798

/-! A coarse bound on the actual paper statistics constant at dimension 12799. -/
namespace BstLean.Part266.Row12799
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12797 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12797 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12797 128 ≤ (13051 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13051 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12799) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12799 : ℕ))
    (by norm_num : (12799 : ℕ) ≤ 16384)
  have ht : paperTail256 12799 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12799 : ℝ) ≤ 114 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12799 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12799 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12799 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12799 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16) := by
    change exactRadius 12797 128 * √(2 / (12799 : ℝ)) *
      (√(12799 : ℝ) + paperT0 12799 + paperTail256 12799) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12799 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12799 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12799 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12797 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12797 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12799 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (114 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12799

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12799
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12799 (61 / 100) 163 (17 / (100 * 12799)) (26 / (10 * 12799)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12799 (61 / 100) 163 (17 / (100 * 12799)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (454663 / 97656250000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (45469853 / 31250000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (961269157 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12799 / 12799 * (61 / 100)) ^ 4 * inverseRadius8 (12799 - 1) /
            envelopeGap 12799 (61 / 100) 163 (17 / (100 * 12799)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12799

namespace BstLean.Part266.Row12799
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12799 163 ≤ (561823981 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12799 163 ≤ (1499471989 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (36039867 / 100000000000000000)
  w0 : (tableEnvelope C).w0 12799 163 ≤ (1790985841 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12799 163 ≤ (637126121 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12799 163 ≤ (29098723 / 6250000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (454663 / 97656250000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (454663 / 97656250000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (45469853 / 31250000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (961269157 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3644487 / 1000000000) : ℝ) ≤ √(17 / (100 * 12799) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12799) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2157718499 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7628984981 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12799) * 163 ≤ 186 / 10000 := by
    have hs : √(tA 12799) ≤ (110494067 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12799) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12799 * (163 : ℝ) ^ 2 + 26 / (10 * 12799) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12799) : ℝ)) (tA 12799 * 163 ^ 2 + 26 / (10 * 12799)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3644487 / 1000000000))) * ((454663 / 97656250000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3644487 / 1000000000)) ^ 3) * ((45469853 / 31250000000000000000000))) + ((961269157 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3644487 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12799) : ℝ)) d.D d.V d.P (√(tA 12799) * 163) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3644487 / 1000000000)) ^ 2 * (((2157718499 / 1000000000000000)) * ((7628984981 / 200000000000000000)))) + ((961269157 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12799) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3644487 / 1000000000)) * ((454663 / 97656250000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12799) : ℝ)) (tA 12799 * 163 ^ 2 + 26 / (10 * 12799)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((454663 / 97656250000000000) : ℝ) + (24198 / 100000) / (2 * ((3644487 / 1000000000)) ^ 2) * ((45469853 / 31250000000000000000000)) + ((961269157 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12799) : ℝ)) (√(26 / (10 * 12799) : ℝ)) d.D d.V d.P (√(tA 12799) * 163) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3644487 / 1000000000)) * (((2157718499 / 1000000000000000)) * ((7628984981 / 200000000000000000))) + ((961269157 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12799) * 163) ≤ _
    unfold AW2
    calc
      _ ≤ ((454663 / 97656250000000000) : ℝ) + ((961269157 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12799

namespace BstLean.Part266.Row12799
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12799 163 ∧
    0 ≤ (tableEnvelope C).f1 12799 163 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12799 163 ∧
    0 ≤ (tableEnvelope C).w1 12799 163 ∧ 0 ≤ (tableEnvelope C).w2 12799 163 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12799 * (163 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12799 163 ∧ 0 ≤ d.f1 12799 163 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12799 163 ∧ 0 ≤ d.w1 12799 163 ∧ 0 ≤ d.w2 12799 163
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12799 ≤ 2 * (228 / 100 : ℝ) / 12799 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12799 ≤ 2 * (370 / 100 : ℝ) / 12799 := by
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
    (completeRAData (tableEnvelope C) 12799 163).locationBound 12799 163 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12799 163).energyBound 12799 163 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12799 163) (d.f1 12799 163) d.f2 ≤
      32 * (((561823981 / 125000000000000000) : ℝ) + (1499471989 / 1000000000000000000) + (36039867 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12799 163) (d.w1 12799 163)
      (d.w2 12799 163) ≤
      32 * (((1790985841 / 100000000000000000000) : ℝ) + (637126121 / 50000000000000000000) + (29098723 / 6250000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12799 163) (d.f1 12799 163) d.f2 ≤
      ((561823981 / 125000000000000000) : ℝ) ^ 2 + 2 * ((561823981 / 125000000000000000)) * ((1499471989 / 1000000000000000000)) * (126 / 100) +
      2 * (((1499471989 / 1000000000000000000)) ^ 2 + 2 * ((561823981 / 125000000000000000)) * ((36039867 / 100000000000000000))) +
      6 * ((1499471989 / 1000000000000000000)) * ((36039867 / 100000000000000000)) * (126 / 100) + 8 * ((36039867 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12799 163) (d.f1 12799 163) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12799 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12799 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12799 163) (d.f1 12799 163) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12799 163) (d.w1 12799 163) (d.w2 12799 163)
  have hwexpr0 : 0 ≤ d.w0 12799 163 + d.w1 12799 163 * √(π / 2) +
      2 * d.w2 12799 163 + energyR16 12799 *
      radiusPolynomialRoot16 (d.w0 12799 163) (d.w1 12799 163) (d.w2 12799 163) := by
    positivity
  constructor
  · change (12799 : ℝ) ^ 8 * (mA 12799 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12799 163) (d.f1 12799 163) d.f2 + locationR16 12799 *
        radiusPolynomialRoot16 (d.f0 12799 163) (d.f1 12799 163) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12799 : ℝ) ^ 8 * (mA 12799 : ℝ) ^ 8 *
        ((((561823981 / 125000000000000000) : ℝ) ^ 2 + 2 * ((561823981 / 125000000000000000)) * ((1499471989 / 1000000000000000000)) * (126 / 100) +
          2 * (((1499471989 / 1000000000000000000)) ^ 2 + 2 * ((561823981 / 125000000000000000)) * ((36039867 / 100000000000000000))) +
          6 * ((1499471989 / 1000000000000000000)) * ((36039867 / 100000000000000000)) * (126 / 100) + 8 * ((36039867 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12799) *
          (32 * (((561823981 / 125000000000000000) : ℝ) + (1499471989 / 1000000000000000000) + (36039867 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12799 : ℝ) ^ 16 *
      (d.w0 12799 163 + d.w1 12799 163 * √(π / 2) + 2 * d.w2 12799 163 +
        energyR16 12799 * radiusPolynomialRoot16 (d.w0 12799 163) (d.w1 12799 163)
          (d.w2 12799 163)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12799 : ℝ) ^ 16 *
        (((1790985841 / 100000000000000000000) : ℝ) + ((637126121 / 50000000000000000000)) * (126 / 100) + 2 * ((29098723 / 6250000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12799) *
          (32 * (((1790985841 / 100000000000000000000) : ℝ) + (637126121 / 50000000000000000000) + (29098723 / 6250000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12799
