import BstLean.Part266Shard5Step4


/-! A coarse bound on the actual paper statistics constant at dimension 12475. -/
namespace BstLean.Part266.Row12475
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12473 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12473 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12473 128 ≤ (12727 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12727 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12475) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12475 : ℕ))
    (by norm_num : (12475 : ℕ) ≤ 16384)
  have ht : paperTail256 12475 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12475 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12475 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12475 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12475 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12475 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12473 128 * √(2 / (12475 : ℝ)) *
      (√(12475 : ℝ) + paperT0 12475 + paperTail256 12475) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12475 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12475 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12475 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12473 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12473 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12475 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12475

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12475
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12475 (61 / 100) 161 (17 / (100 * 12475)) (26 / (10 * 12475)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12475 (61 / 100) 161 (17 / (100 * 12475)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (100560583 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1612193741 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5906879719 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12475 / 12475 * (61 / 100)) ^ 4 * inverseRadius8 (12475 - 1) /
            envelopeGap 12475 (61 / 100) 161 (17 / (100 * 12475)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12475

namespace BstLean.Part266.Row12475
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12475 161 ≤ (2396076557 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12475 161 ≤ (1598743591 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (76851727 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12475 161 ≤ (96709777 / 5000000000000000000)
  w1 : (tableEnvelope C).w1 12475 161 ≤ (688071617 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12475 161 ≤ (502808637 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (100560583 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (100560583 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1612193741 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5906879719 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3691511 / 1000000000) : ℝ) ≤ √(17 / (100 * 12475) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12475) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2242326727 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40152132459 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12475) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12475) ≤ (113363813 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12475) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12475 * (161 : ℝ) ^ 2 + 26 / (10 * 12475) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12475) : ℝ)) (tA 12475 * 161 ^ 2 + 26 / (10 * 12475)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3691511 / 1000000000))) * ((100560583 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3691511 / 1000000000)) ^ 3) * ((1612193741 / 1000000000000000000000000))) + ((5906879719 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3691511 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12475) : ℝ)) d.D d.V d.P (√(tA 12475) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3691511 / 1000000000)) ^ 2 * (((2242326727 / 1000000000000000)) * ((40152132459 / 1000000000000000000)))) + ((5906879719 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12475) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3691511 / 1000000000)) * ((100560583 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12475) : ℝ)) (tA 12475 * 161 ^ 2 + 26 / (10 * 12475)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((100560583 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3691511 / 1000000000)) ^ 2) * ((1612193741 / 1000000000000000000000000)) + ((5906879719 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12475) : ℝ)) (√(26 / (10 * 12475) : ℝ)) d.D d.V d.P (√(tA 12475) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3691511 / 1000000000)) * (((2242326727 / 1000000000000000)) * ((40152132459 / 1000000000000000000))) + ((5906879719 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12475) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((100560583 / 20000000000000000000) : ℝ) + ((5906879719 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12475

namespace BstLean.Part266.Row12475
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12475 161 ∧
    0 ≤ (tableEnvelope C).f1 12475 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12475 161 ∧
    0 ≤ (tableEnvelope C).w1 12475 161 ∧ 0 ≤ (tableEnvelope C).w2 12475 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12475 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12475 161 ∧ 0 ≤ d.f1 12475 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12475 161 ∧ 0 ≤ d.w1 12475 161 ∧ 0 ≤ d.w2 12475 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12475 ≤ 2 * (228 / 100 : ℝ) / 12475 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12475 ≤ 2 * (370 / 100 : ℝ) / 12475 := by
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
    (completeRAData (tableEnvelope C) 12475 161).locationBound 12475 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12475 161).energyBound 12475 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12475 161) (d.f1 12475 161) d.f2 ≤
      32 * (((2396076557 / 500000000000000000) : ℝ) + (1598743591 / 1000000000000000000) + (76851727 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12475 161) (d.w1 12475 161)
      (d.w2 12475 161) ≤
      32 * (((96709777 / 5000000000000000000) : ℝ) + (688071617 / 50000000000000000000) + (502808637 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12475 161) (d.f1 12475 161) d.f2 ≤
      ((2396076557 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2396076557 / 500000000000000000)) * ((1598743591 / 1000000000000000000)) * (126 / 100) +
      2 * (((1598743591 / 1000000000000000000)) ^ 2 + 2 * ((2396076557 / 500000000000000000)) * ((76851727 / 200000000000000000))) +
      6 * ((1598743591 / 1000000000000000000)) * ((76851727 / 200000000000000000)) * (126 / 100) + 8 * ((76851727 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12475 161) (d.f1 12475 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12475 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12475 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12475 161) (d.f1 12475 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12475 161) (d.w1 12475 161) (d.w2 12475 161)
  have hwexpr0 : 0 ≤ d.w0 12475 161 + d.w1 12475 161 * √(π / 2) +
      2 * d.w2 12475 161 + energyR16 12475 *
      radiusPolynomialRoot16 (d.w0 12475 161) (d.w1 12475 161) (d.w2 12475 161) := by
    positivity
  constructor
  · change (12475 : ℝ) ^ 8 * (mA 12475 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12475 161) (d.f1 12475 161) d.f2 + locationR16 12475 *
        radiusPolynomialRoot16 (d.f0 12475 161) (d.f1 12475 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12475 : ℝ) ^ 8 * (mA 12475 : ℝ) ^ 8 *
        ((((2396076557 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2396076557 / 500000000000000000)) * ((1598743591 / 1000000000000000000)) * (126 / 100) +
          2 * (((1598743591 / 1000000000000000000)) ^ 2 + 2 * ((2396076557 / 500000000000000000)) * ((76851727 / 200000000000000000))) +
          6 * ((1598743591 / 1000000000000000000)) * ((76851727 / 200000000000000000)) * (126 / 100) + 8 * ((76851727 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12475) *
          (32 * (((2396076557 / 500000000000000000) : ℝ) + (1598743591 / 1000000000000000000) + (76851727 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12475 : ℝ) ^ 16 *
      (d.w0 12475 161 + d.w1 12475 161 * √(π / 2) + 2 * d.w2 12475 161 +
        energyR16 12475 * radiusPolynomialRoot16 (d.w0 12475 161) (d.w1 12475 161)
          (d.w2 12475 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12475 : ℝ) ^ 16 *
        (((96709777 / 5000000000000000000) : ℝ) + ((688071617 / 50000000000000000000)) * (126 / 100) + 2 * ((502808637 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12475) *
          (32 * (((96709777 / 5000000000000000000) : ℝ) + (688071617 / 50000000000000000000) + (502808637 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12475

/-! A coarse bound on the actual paper statistics constant at dimension 12476. -/
namespace BstLean.Part266.Row12476
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12474 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12474 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12474 128 ≤ (12728 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12728 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12476) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12476 : ℕ))
    (by norm_num : (12476 : ℕ) ≤ 16384)
  have ht : paperTail256 12476 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12476 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12476 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12476 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12476 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12476 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12474 128 * √(2 / (12476 : ℝ)) *
      (√(12476 : ℝ) + paperT0 12476 + paperTail256 12476) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12476 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12476 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12476 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12474 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12474 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12476 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12476

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12476
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12476 (61 / 100) 161 (17 / (100 * 12476)) (26 / (10 * 12476)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12476 (61 / 100) 161 (17 / (100 * 12476)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (251341007 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (201459611 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2951527909 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12476 / 12476 * (61 / 100)) ^ 4 * inverseRadius8 (12476 - 1) /
            envelopeGap 12476 (61 / 100) 161 (17 / (100 * 12476)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12476

namespace BstLean.Part266.Row12476
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12476 161 ≤ (598899129 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12476 161 ≤ (199802909 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (384181641 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12476 161 ≤ (966865247 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12476 161 ≤ (687906177 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12476 161 ≤ (502687733 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (251341007 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (251341007 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (201459611 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2951527909 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3691363 / 1000000000) : ℝ) ≤ √(17 / (100 * 12476) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12476) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2242057123 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (501821197 / 12500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12476) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12476) ≤ (113354727 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12476) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12476 * (161 : ℝ) ^ 2 + 26 / (10 * 12476) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12476) : ℝ)) (tA 12476 * 161 ^ 2 + 26 / (10 * 12476)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3691363 / 1000000000))) * ((251341007 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3691363 / 1000000000)) ^ 3) * ((201459611 / 125000000000000000000000))) + ((2951527909 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3691363 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12476) : ℝ)) d.D d.V d.P (√(tA 12476) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3691363 / 1000000000)) ^ 2 * (((2242057123 / 1000000000000000)) * ((501821197 / 12500000000000000)))) + ((2951527909 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12476) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3691363 / 1000000000)) * ((251341007 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12476) : ℝ)) (tA 12476 * 161 ^ 2 + 26 / (10 * 12476)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((251341007 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3691363 / 1000000000)) ^ 2) * ((201459611 / 125000000000000000000000)) + ((2951527909 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12476) : ℝ)) (√(26 / (10 * 12476) : ℝ)) d.D d.V d.P (√(tA 12476) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3691363 / 1000000000)) * (((2242057123 / 1000000000000000)) * ((501821197 / 12500000000000000))) + ((2951527909 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12476) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((251341007 / 50000000000000000000) : ℝ) + ((2951527909 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12476

namespace BstLean.Part266.Row12476
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12476 161 ∧
    0 ≤ (tableEnvelope C).f1 12476 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12476 161 ∧
    0 ≤ (tableEnvelope C).w1 12476 161 ∧ 0 ≤ (tableEnvelope C).w2 12476 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12476 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12476 161 ∧ 0 ≤ d.f1 12476 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12476 161 ∧ 0 ≤ d.w1 12476 161 ∧ 0 ≤ d.w2 12476 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12476 ≤ 2 * (228 / 100 : ℝ) / 12476 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12476 ≤ 2 * (370 / 100 : ℝ) / 12476 := by
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
    (completeRAData (tableEnvelope C) 12476 161).locationBound 12476 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12476 161).energyBound 12476 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12476 161) (d.f1 12476 161) d.f2 ≤
      32 * (((598899129 / 125000000000000000) : ℝ) + (199802909 / 125000000000000000) + (384181641 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12476 161) (d.w1 12476 161)
      (d.w2 12476 161) ≤
      32 * (((966865247 / 50000000000000000000) : ℝ) + (687906177 / 50000000000000000000) + (502687733 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12476 161) (d.f1 12476 161) d.f2 ≤
      ((598899129 / 125000000000000000) : ℝ) ^ 2 + 2 * ((598899129 / 125000000000000000)) * ((199802909 / 125000000000000000)) * (126 / 100) +
      2 * (((199802909 / 125000000000000000)) ^ 2 + 2 * ((598899129 / 125000000000000000)) * ((384181641 / 1000000000000000000))) +
      6 * ((199802909 / 125000000000000000)) * ((384181641 / 1000000000000000000)) * (126 / 100) + 8 * ((384181641 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12476 161) (d.f1 12476 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12476 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12476 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12476 161) (d.f1 12476 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12476 161) (d.w1 12476 161) (d.w2 12476 161)
  have hwexpr0 : 0 ≤ d.w0 12476 161 + d.w1 12476 161 * √(π / 2) +
      2 * d.w2 12476 161 + energyR16 12476 *
      radiusPolynomialRoot16 (d.w0 12476 161) (d.w1 12476 161) (d.w2 12476 161) := by
    positivity
  constructor
  · change (12476 : ℝ) ^ 8 * (mA 12476 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12476 161) (d.f1 12476 161) d.f2 + locationR16 12476 *
        radiusPolynomialRoot16 (d.f0 12476 161) (d.f1 12476 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12476 : ℝ) ^ 8 * (mA 12476 : ℝ) ^ 8 *
        ((((598899129 / 125000000000000000) : ℝ) ^ 2 + 2 * ((598899129 / 125000000000000000)) * ((199802909 / 125000000000000000)) * (126 / 100) +
          2 * (((199802909 / 125000000000000000)) ^ 2 + 2 * ((598899129 / 125000000000000000)) * ((384181641 / 1000000000000000000))) +
          6 * ((199802909 / 125000000000000000)) * ((384181641 / 1000000000000000000)) * (126 / 100) + 8 * ((384181641 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12476) *
          (32 * (((598899129 / 125000000000000000) : ℝ) + (199802909 / 125000000000000000) + (384181641 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12476 : ℝ) ^ 16 *
      (d.w0 12476 161 + d.w1 12476 161 * √(π / 2) + 2 * d.w2 12476 161 +
        energyR16 12476 * radiusPolynomialRoot16 (d.w0 12476 161) (d.w1 12476 161)
          (d.w2 12476 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12476 : ℝ) ^ 16 *
        (((966865247 / 50000000000000000000) : ℝ) + ((687906177 / 50000000000000000000)) * (126 / 100) + 2 * ((502687733 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12476) *
          (32 * (((966865247 / 50000000000000000000) : ℝ) + (687906177 / 50000000000000000000) + (502687733 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12476

/-! A coarse bound on the actual paper statistics constant at dimension 12477. -/
namespace BstLean.Part266.Row12477
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12475 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12475 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12475 128 ≤ (12729 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12729 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12477) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12477 : ℕ))
    (by norm_num : (12477 : ℕ) ≤ 16384)
  have ht : paperTail256 12477 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12477 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12477 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12477 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12477 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12477 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12475 128 * √(2 / (12477 : ℝ)) *
      (√(12477 : ℝ) + paperT0 12477 + paperTail256 12477) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12477 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12477 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12477 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12475 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12475 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12477 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12477

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12477
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12477 (61 / 100) 161 (17 / (100 * 12477)) (26 / (10 * 12477)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12477 (61 / 100) 161 (17 / (100 * 12477)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (502561151 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (805580121 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (368702169 / 62500000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12477 / 12477 * (61 / 100)) ^ 4 * inverseRadius8 (12477 - 1) /
            envelopeGap 12477 (61 / 100) 161 (17 / (100 * 12477)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12477

namespace BstLean.Part266.Row12477
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12477 161 ≤ (2395116643 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12477 161 ≤ (1598103057 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (38410467 / 100000000000000000)
  w0 : (tableEnvelope C).w0 12477 161 ≤ (1933265609 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12477 161 ≤ (275096317 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12477 161 ≤ (251283433 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (502561151 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (502561151 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (805580121 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (368702169 / 62500000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((738243 / 200000000) : ℝ) ≤ √(17 / (100 * 12477) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12477) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2241787571 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40139260607 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12477) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12477) ≤ (113345641 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12477) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12477 * (161 : ℝ) ^ 2 + 26 / (10 * 12477) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12477) : ℝ)) (tA 12477 * 161 ^ 2 + 26 / (10 * 12477)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((738243 / 200000000))) * ((502561151 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((738243 / 200000000)) ^ 3) * ((805580121 / 500000000000000000000000))) + ((368702169 / 62500000000000000000000)) * (3 / 2 * (39895 / 100000) / ((738243 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12477) : ℝ)) d.D d.V d.P (√(tA 12477) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((738243 / 200000000)) ^ 2 * (((2241787571 / 1000000000000000)) * ((40139260607 / 1000000000000000000)))) + ((368702169 / 62500000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12477) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((738243 / 200000000)) * ((502561151 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12477) : ℝ)) (tA 12477 * 161 ^ 2 + 26 / (10 * 12477)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((502561151 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((738243 / 200000000)) ^ 2) * ((805580121 / 500000000000000000000000)) + ((368702169 / 62500000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12477) : ℝ)) (√(26 / (10 * 12477) : ℝ)) d.D d.V d.P (√(tA 12477) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((738243 / 200000000)) * (((2241787571 / 1000000000000000)) * ((40139260607 / 1000000000000000000))) + ((368702169 / 62500000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12477) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((502561151 / 100000000000000000000) : ℝ) + ((368702169 / 62500000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12477

namespace BstLean.Part266.Row12477
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12477 161 ∧
    0 ≤ (tableEnvelope C).f1 12477 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12477 161 ∧
    0 ≤ (tableEnvelope C).w1 12477 161 ∧ 0 ≤ (tableEnvelope C).w2 12477 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12477 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12477 161 ∧ 0 ≤ d.f1 12477 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12477 161 ∧ 0 ≤ d.w1 12477 161 ∧ 0 ≤ d.w2 12477 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12477 ≤ 2 * (228 / 100 : ℝ) / 12477 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12477 ≤ 2 * (370 / 100 : ℝ) / 12477 := by
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
    (completeRAData (tableEnvelope C) 12477 161).locationBound 12477 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12477 161).energyBound 12477 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12477 161) (d.f1 12477 161) d.f2 ≤
      32 * (((2395116643 / 500000000000000000) : ℝ) + (1598103057 / 1000000000000000000) + (38410467 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12477 161) (d.w1 12477 161)
      (d.w2 12477 161) ≤
      32 * (((1933265609 / 100000000000000000000) : ℝ) + (275096317 / 20000000000000000000) + (251283433 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12477 161) (d.f1 12477 161) d.f2 ≤
      ((2395116643 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2395116643 / 500000000000000000)) * ((1598103057 / 1000000000000000000)) * (126 / 100) +
      2 * (((1598103057 / 1000000000000000000)) ^ 2 + 2 * ((2395116643 / 500000000000000000)) * ((38410467 / 100000000000000000))) +
      6 * ((1598103057 / 1000000000000000000)) * ((38410467 / 100000000000000000)) * (126 / 100) + 8 * ((38410467 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12477 161) (d.f1 12477 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12477 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12477 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12477 161) (d.f1 12477 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12477 161) (d.w1 12477 161) (d.w2 12477 161)
  have hwexpr0 : 0 ≤ d.w0 12477 161 + d.w1 12477 161 * √(π / 2) +
      2 * d.w2 12477 161 + energyR16 12477 *
      radiusPolynomialRoot16 (d.w0 12477 161) (d.w1 12477 161) (d.w2 12477 161) := by
    positivity
  constructor
  · change (12477 : ℝ) ^ 8 * (mA 12477 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12477 161) (d.f1 12477 161) d.f2 + locationR16 12477 *
        radiusPolynomialRoot16 (d.f0 12477 161) (d.f1 12477 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12477 : ℝ) ^ 8 * (mA 12477 : ℝ) ^ 8 *
        ((((2395116643 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2395116643 / 500000000000000000)) * ((1598103057 / 1000000000000000000)) * (126 / 100) +
          2 * (((1598103057 / 1000000000000000000)) ^ 2 + 2 * ((2395116643 / 500000000000000000)) * ((38410467 / 100000000000000000))) +
          6 * ((1598103057 / 1000000000000000000)) * ((38410467 / 100000000000000000)) * (126 / 100) + 8 * ((38410467 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12477) *
          (32 * (((2395116643 / 500000000000000000) : ℝ) + (1598103057 / 1000000000000000000) + (38410467 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12477 : ℝ) ^ 16 *
      (d.w0 12477 161 + d.w1 12477 161 * √(π / 2) + 2 * d.w2 12477 161 +
        energyR16 12477 * radiusPolynomialRoot16 (d.w0 12477 161) (d.w1 12477 161)
          (d.w2 12477 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12477 : ℝ) ^ 16 *
        (((1933265609 / 100000000000000000000) : ℝ) + ((275096317 / 20000000000000000000)) * (126 / 100) + 2 * ((251283433 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12477) *
          (32 * (((1933265609 / 100000000000000000000) : ℝ) + (275096317 / 20000000000000000000) + (251283433 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12477

/-! A coarse bound on the actual paper statistics constant at dimension 12478. -/
namespace BstLean.Part266.Row12478
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12476 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12476 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12476 128 ≤ (12730 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12730 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12478) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12478 : ℕ))
    (by norm_num : (12478 : ℕ) ≤ 16384)
  have ht : paperTail256 12478 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12478 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12478 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12478 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12478 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12478 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12476 128 * √(2 / (12478 : ℝ)) *
      (√(12478 : ℝ) + paperT0 12478 + paperTail256 12478) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12478 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12478 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12478 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12476 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12476 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12478 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12478

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12478
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12478 (61 / 100) 161 (17 / (100 * 12478)) (26 / (10 * 12478)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12478 (61 / 100) 161 (17 / (100 * 12478)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (502440327 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1610643803 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (736927047 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12478 / 12478 * (61 / 100)) ^ 4 * inverseRadius8 (12478 - 1) /
            envelopeGap 12478 (61 / 100) 161 (17 / (100 * 12478)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12478

namespace BstLean.Part266.Row12478
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12478 161 ≤ (1197318469 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12478 161 ≤ (399445737 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (384027723 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12478 161 ≤ (1932800887 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12478 161 ≤ (85946933 / 6250000000000000000)
  w2 : (tableEnvelope C).w2 12478 161 ≤ (251223019 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (502440327 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (502440327 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1610643803 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (736927047 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3691067 / 1000000000) : ℝ) ≤ √(17 / (100 * 12478) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12478) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2241518073 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40132827 / 1000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12478) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12478) ≤ (56668279 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12478) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12478 * (161 : ℝ) ^ 2 + 26 / (10 * 12478) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12478) : ℝ)) (tA 12478 * 161 ^ 2 + 26 / (10 * 12478)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3691067 / 1000000000))) * ((502440327 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3691067 / 1000000000)) ^ 3) * ((1610643803 / 1000000000000000000000000))) + ((736927047 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3691067 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12478) : ℝ)) d.D d.V d.P (√(tA 12478) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3691067 / 1000000000)) ^ 2 * (((2241518073 / 1000000000000000)) * ((40132827 / 1000000000000000)))) + ((736927047 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12478) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3691067 / 1000000000)) * ((502440327 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12478) : ℝ)) (tA 12478 * 161 ^ 2 + 26 / (10 * 12478)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((502440327 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3691067 / 1000000000)) ^ 2) * ((1610643803 / 1000000000000000000000000)) + ((736927047 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12478) : ℝ)) (√(26 / (10 * 12478) : ℝ)) d.D d.V d.P (√(tA 12478) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3691067 / 1000000000)) * (((2241518073 / 1000000000000000)) * ((40132827 / 1000000000000000))) + ((736927047 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12478) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((502440327 / 100000000000000000000) : ℝ) + ((736927047 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12478

namespace BstLean.Part266.Row12478
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12478 161 ∧
    0 ≤ (tableEnvelope C).f1 12478 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12478 161 ∧
    0 ≤ (tableEnvelope C).w1 12478 161 ∧ 0 ≤ (tableEnvelope C).w2 12478 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12478 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12478 161 ∧ 0 ≤ d.f1 12478 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12478 161 ∧ 0 ≤ d.w1 12478 161 ∧ 0 ≤ d.w2 12478 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12478 ≤ 2 * (228 / 100 : ℝ) / 12478 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12478 ≤ 2 * (370 / 100 : ℝ) / 12478 := by
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
    (completeRAData (tableEnvelope C) 12478 161).locationBound 12478 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12478 161).energyBound 12478 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12478 161) (d.f1 12478 161) d.f2 ≤
      32 * (((1197318469 / 250000000000000000) : ℝ) + (399445737 / 250000000000000000) + (384027723 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12478 161) (d.w1 12478 161)
      (d.w2 12478 161) ≤
      32 * (((1932800887 / 100000000000000000000) : ℝ) + (85946933 / 6250000000000000000) + (251223019 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12478 161) (d.f1 12478 161) d.f2 ≤
      ((1197318469 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1197318469 / 250000000000000000)) * ((399445737 / 250000000000000000)) * (126 / 100) +
      2 * (((399445737 / 250000000000000000)) ^ 2 + 2 * ((1197318469 / 250000000000000000)) * ((384027723 / 1000000000000000000))) +
      6 * ((399445737 / 250000000000000000)) * ((384027723 / 1000000000000000000)) * (126 / 100) + 8 * ((384027723 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12478 161) (d.f1 12478 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12478 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12478 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12478 161) (d.f1 12478 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12478 161) (d.w1 12478 161) (d.w2 12478 161)
  have hwexpr0 : 0 ≤ d.w0 12478 161 + d.w1 12478 161 * √(π / 2) +
      2 * d.w2 12478 161 + energyR16 12478 *
      radiusPolynomialRoot16 (d.w0 12478 161) (d.w1 12478 161) (d.w2 12478 161) := by
    positivity
  constructor
  · change (12478 : ℝ) ^ 8 * (mA 12478 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12478 161) (d.f1 12478 161) d.f2 + locationR16 12478 *
        radiusPolynomialRoot16 (d.f0 12478 161) (d.f1 12478 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12478 : ℝ) ^ 8 * (mA 12478 : ℝ) ^ 8 *
        ((((1197318469 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1197318469 / 250000000000000000)) * ((399445737 / 250000000000000000)) * (126 / 100) +
          2 * (((399445737 / 250000000000000000)) ^ 2 + 2 * ((1197318469 / 250000000000000000)) * ((384027723 / 1000000000000000000))) +
          6 * ((399445737 / 250000000000000000)) * ((384027723 / 1000000000000000000)) * (126 / 100) + 8 * ((384027723 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12478) *
          (32 * (((1197318469 / 250000000000000000) : ℝ) + (399445737 / 250000000000000000) + (384027723 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12478 : ℝ) ^ 16 *
      (d.w0 12478 161 + d.w1 12478 161 * √(π / 2) + 2 * d.w2 12478 161 +
        energyR16 12478 * radiusPolynomialRoot16 (d.w0 12478 161) (d.w1 12478 161)
          (d.w2 12478 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12478 : ℝ) ^ 16 *
        (((1932800887 / 100000000000000000000) : ℝ) + ((85946933 / 6250000000000000000)) * (126 / 100) + 2 * ((251223019 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12478) *
          (32 * (((1932800887 / 100000000000000000000) : ℝ) + (85946933 / 6250000000000000000) + (251223019 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12478

/-! A coarse bound on the actual paper statistics constant at dimension 12479. -/
namespace BstLean.Part266.Row12479
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12477 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12477 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12477 128 ≤ (12731 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12731 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12479) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12479 : ℕ))
    (by norm_num : (12479 : ℕ) ≤ 16384)
  have ht : paperTail256 12479 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12479 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12479 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12479 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12479 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12479 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12477 128 * √(2 / (12479 : ℝ)) *
      (√(12479 : ℝ) + paperT0 12479 + paperTail256 12479) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12479 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12479 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12479 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12477 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12477 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12479 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12479

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12479
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12479 (61 / 100) 161 (17 / (100 * 12479)) (26 / (10 * 12479)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12479 (61 / 100) 161 (17 / (100 * 12479)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (502319541 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1610127571 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5891600831 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12479 / 12479 * (61 / 100)) ^ 4 * inverseRadius8 (12479 - 1) /
            envelopeGap 12479 (61 / 100) 161 (17 / (100 * 12479)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12479

namespace BstLean.Part266.Row12479
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12479 161 ≤ (2394157401 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12479 161 ≤ (1597462943 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (191975399 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12479 161 ≤ (241542041 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12479 161 ≤ (42963137 / 3125000000000000000)
  w2 : (tableEnvelope C).w2 12479 161 ≤ (502325249 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (502319541 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (502319541 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1610127571 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5891600831 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3690919 / 1000000000) : ℝ) ≤ √(17 / (100 * 12479) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12479) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (560312157 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (20063197471 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12479) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12479) ≤ (28331869 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12479) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12479 * (161 : ℝ) ^ 2 + 26 / (10 * 12479) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12479) : ℝ)) (tA 12479 * 161 ^ 2 + 26 / (10 * 12479)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3690919 / 1000000000))) * ((502319541 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3690919 / 1000000000)) ^ 3) * ((1610127571 / 1000000000000000000000000))) + ((5891600831 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3690919 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12479) : ℝ)) d.D d.V d.P (√(tA 12479) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3690919 / 1000000000)) ^ 2 * (((560312157 / 250000000000000)) * ((20063197471 / 500000000000000000)))) + ((5891600831 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12479) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3690919 / 1000000000)) * ((502319541 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12479) : ℝ)) (tA 12479 * 161 ^ 2 + 26 / (10 * 12479)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((502319541 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3690919 / 1000000000)) ^ 2) * ((1610127571 / 1000000000000000000000000)) + ((5891600831 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12479) : ℝ)) (√(26 / (10 * 12479) : ℝ)) d.D d.V d.P (√(tA 12479) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3690919 / 1000000000)) * (((560312157 / 250000000000000)) * ((20063197471 / 500000000000000000))) + ((5891600831 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12479) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((502319541 / 100000000000000000000) : ℝ) + ((5891600831 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12479

namespace BstLean.Part266.Row12479
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12479 161 ∧
    0 ≤ (tableEnvelope C).f1 12479 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12479 161 ∧
    0 ≤ (tableEnvelope C).w1 12479 161 ∧ 0 ≤ (tableEnvelope C).w2 12479 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12479 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12479 161 ∧ 0 ≤ d.f1 12479 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12479 161 ∧ 0 ≤ d.w1 12479 161 ∧ 0 ≤ d.w2 12479 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12479 ≤ 2 * (228 / 100 : ℝ) / 12479 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12479 ≤ 2 * (370 / 100 : ℝ) / 12479 := by
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
    (completeRAData (tableEnvelope C) 12479 161).locationBound 12479 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12479 161).energyBound 12479 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12479 161) (d.f1 12479 161) d.f2 ≤
      32 * (((2394157401 / 500000000000000000) : ℝ) + (1597462943 / 1000000000000000000) + (191975399 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12479 161) (d.w1 12479 161)
      (d.w2 12479 161) ≤
      32 * (((241542041 / 12500000000000000000) : ℝ) + (42963137 / 3125000000000000000) + (502325249 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12479 161) (d.f1 12479 161) d.f2 ≤
      ((2394157401 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2394157401 / 500000000000000000)) * ((1597462943 / 1000000000000000000)) * (126 / 100) +
      2 * (((1597462943 / 1000000000000000000)) ^ 2 + 2 * ((2394157401 / 500000000000000000)) * ((191975399 / 500000000000000000))) +
      6 * ((1597462943 / 1000000000000000000)) * ((191975399 / 500000000000000000)) * (126 / 100) + 8 * ((191975399 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12479 161) (d.f1 12479 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12479 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12479 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12479 161) (d.f1 12479 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12479 161) (d.w1 12479 161) (d.w2 12479 161)
  have hwexpr0 : 0 ≤ d.w0 12479 161 + d.w1 12479 161 * √(π / 2) +
      2 * d.w2 12479 161 + energyR16 12479 *
      radiusPolynomialRoot16 (d.w0 12479 161) (d.w1 12479 161) (d.w2 12479 161) := by
    positivity
  constructor
  · change (12479 : ℝ) ^ 8 * (mA 12479 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12479 161) (d.f1 12479 161) d.f2 + locationR16 12479 *
        radiusPolynomialRoot16 (d.f0 12479 161) (d.f1 12479 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12479 : ℝ) ^ 8 * (mA 12479 : ℝ) ^ 8 *
        ((((2394157401 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2394157401 / 500000000000000000)) * ((1597462943 / 1000000000000000000)) * (126 / 100) +
          2 * (((1597462943 / 1000000000000000000)) ^ 2 + 2 * ((2394157401 / 500000000000000000)) * ((191975399 / 500000000000000000))) +
          6 * ((1597462943 / 1000000000000000000)) * ((191975399 / 500000000000000000)) * (126 / 100) + 8 * ((191975399 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12479) *
          (32 * (((2394157401 / 500000000000000000) : ℝ) + (1597462943 / 1000000000000000000) + (191975399 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12479 : ℝ) ^ 16 *
      (d.w0 12479 161 + d.w1 12479 161 * √(π / 2) + 2 * d.w2 12479 161 +
        energyR16 12479 * radiusPolynomialRoot16 (d.w0 12479 161) (d.w1 12479 161)
          (d.w2 12479 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12479 : ℝ) ^ 16 *
        (((241542041 / 12500000000000000000) : ℝ) + ((42963137 / 3125000000000000000)) * (126 / 100) + 2 * ((502325249 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12479) *
          (32 * (((241542041 / 12500000000000000000) : ℝ) + (42963137 / 3125000000000000000) + (502325249 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12479

/-! A coarse bound on the actual paper statistics constant at dimension 12480. -/
namespace BstLean.Part266.Row12480
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12478 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12478 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12478 128 ≤ (12732 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12732 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12480) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12480 : ℕ))
    (by norm_num : (12480 : ℕ) ≤ 16384)
  have ht : paperTail256 12480 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12480 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12480 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12480 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12480 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12480 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12478 128 * √(2 / (12480 : ℝ)) *
      (√(12480 : ℝ) + paperT0 12480 + paperTail256 12480) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12480 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12480 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12480 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12478 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12478 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12480 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12480

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12480
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12480 (61 / 100) 161 (17 / (100 * 12480)) (26 / (10 * 12480)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12480 (61 / 100) 161 (17 / (100 * 12480)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (100439759 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (804805773 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2943894033 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12480 / 12480 * (61 / 100)) ^ 4 * inverseRadius8 (12480 - 1) /
            envelopeGap 12480 (61 / 100) 161 (17 / (100 * 12480)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12480

namespace BstLean.Part266.Row12480
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12480 161 ≤ (149604877 / 31250000000000000)
  f1 : (tableEnvelope C).f1 12480 161 ≤ (319428609 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (191936949 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12480 161 ≤ (482967983 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 12480 161 ≤ (687244977 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12480 161 ≤ (502204499 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (100439759 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (100439759 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (804805773 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2943894033 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3690771 / 1000000000) : ℝ) ≤ √(17 / (100 * 12480) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12480) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (56024481 / 25000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (2507497777 / 62500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12480) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12480) ≤ (22663679 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12480) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12480 * (161 : ℝ) ^ 2 + 26 / (10 * 12480) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12480) : ℝ)) (tA 12480 * 161 ^ 2 + 26 / (10 * 12480)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3690771 / 1000000000))) * ((100439759 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3690771 / 1000000000)) ^ 3) * ((804805773 / 500000000000000000000000))) + ((2943894033 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3690771 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12480) : ℝ)) d.D d.V d.P (√(tA 12480) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3690771 / 1000000000)) ^ 2 * (((56024481 / 25000000000000)) * ((2507497777 / 62500000000000000)))) + ((2943894033 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12480) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3690771 / 1000000000)) * ((100439759 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12480) : ℝ)) (tA 12480 * 161 ^ 2 + 26 / (10 * 12480)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((100439759 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3690771 / 1000000000)) ^ 2) * ((804805773 / 500000000000000000000000)) + ((2943894033 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12480) : ℝ)) (√(26 / (10 * 12480) : ℝ)) d.D d.V d.P (√(tA 12480) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3690771 / 1000000000)) * (((56024481 / 25000000000000)) * ((2507497777 / 62500000000000000))) + ((2943894033 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12480) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((100439759 / 20000000000000000000) : ℝ) + ((2943894033 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12480

namespace BstLean.Part266.Row12480
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12480 161 ∧
    0 ≤ (tableEnvelope C).f1 12480 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12480 161 ∧
    0 ≤ (tableEnvelope C).w1 12480 161 ∧ 0 ≤ (tableEnvelope C).w2 12480 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12480 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12480 161 ∧ 0 ≤ d.f1 12480 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12480 161 ∧ 0 ≤ d.w1 12480 161 ∧ 0 ≤ d.w2 12480 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12480 ≤ 2 * (228 / 100 : ℝ) / 12480 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12480 ≤ 2 * (370 / 100 : ℝ) / 12480 := by
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
    (completeRAData (tableEnvelope C) 12480 161).locationBound 12480 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12480 161).energyBound 12480 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12480 161) (d.f1 12480 161) d.f2 ≤
      32 * (((149604877 / 31250000000000000) : ℝ) + (319428609 / 200000000000000000) + (191936949 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12480 161) (d.w1 12480 161)
      (d.w2 12480 161) ≤
      32 * (((482967983 / 25000000000000000000) : ℝ) + (687244977 / 50000000000000000000) + (502204499 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12480 161) (d.f1 12480 161) d.f2 ≤
      ((149604877 / 31250000000000000) : ℝ) ^ 2 + 2 * ((149604877 / 31250000000000000)) * ((319428609 / 200000000000000000)) * (126 / 100) +
      2 * (((319428609 / 200000000000000000)) ^ 2 + 2 * ((149604877 / 31250000000000000)) * ((191936949 / 500000000000000000))) +
      6 * ((319428609 / 200000000000000000)) * ((191936949 / 500000000000000000)) * (126 / 100) + 8 * ((191936949 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12480 161) (d.f1 12480 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12480 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12480 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12480 161) (d.f1 12480 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12480 161) (d.w1 12480 161) (d.w2 12480 161)
  have hwexpr0 : 0 ≤ d.w0 12480 161 + d.w1 12480 161 * √(π / 2) +
      2 * d.w2 12480 161 + energyR16 12480 *
      radiusPolynomialRoot16 (d.w0 12480 161) (d.w1 12480 161) (d.w2 12480 161) := by
    positivity
  constructor
  · change (12480 : ℝ) ^ 8 * (mA 12480 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12480 161) (d.f1 12480 161) d.f2 + locationR16 12480 *
        radiusPolynomialRoot16 (d.f0 12480 161) (d.f1 12480 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12480 : ℝ) ^ 8 * (mA 12480 : ℝ) ^ 8 *
        ((((149604877 / 31250000000000000) : ℝ) ^ 2 + 2 * ((149604877 / 31250000000000000)) * ((319428609 / 200000000000000000)) * (126 / 100) +
          2 * (((319428609 / 200000000000000000)) ^ 2 + 2 * ((149604877 / 31250000000000000)) * ((191936949 / 500000000000000000))) +
          6 * ((319428609 / 200000000000000000)) * ((191936949 / 500000000000000000)) * (126 / 100) + 8 * ((191936949 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12480) *
          (32 * (((149604877 / 31250000000000000) : ℝ) + (319428609 / 200000000000000000) + (191936949 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12480 : ℝ) ^ 16 *
      (d.w0 12480 161 + d.w1 12480 161 * √(π / 2) + 2 * d.w2 12480 161 +
        energyR16 12480 * radiusPolynomialRoot16 (d.w0 12480 161) (d.w1 12480 161)
          (d.w2 12480 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12480 : ℝ) ^ 16 *
        (((482967983 / 25000000000000000000) : ℝ) + ((687244977 / 50000000000000000000)) * (126 / 100) + 2 * ((502204499 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12480) *
          (32 * (((482967983 / 25000000000000000000) : ℝ) + (687244977 / 50000000000000000000) + (502204499 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12480

/-! A coarse bound on the actual paper statistics constant at dimension 12481. -/
namespace BstLean.Part266.Row12481
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12479 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12479 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12479 128 ≤ (12733 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12733 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12481) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12481 : ℕ))
    (by norm_num : (12481 : ℕ) ≤ 16384)
  have ht : paperTail256 12481 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12481 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12481 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12481 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12481 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12481 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12479 128 * √(2 / (12481 : ℝ)) *
      (√(12481 : ℝ) + paperT0 12481 + paperTail256 12481) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12481 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12481 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12481 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12479 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12479 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12481 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12481

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12481
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12481 (61 / 100) 161 (17 / (100 * 12481)) (26 / (10 * 12481)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12481 (61 / 100) 161 (17 / (100 * 12481)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (502078087 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1609095727 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (36774863 / 6250000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12481 / 12481 * (61 / 100)) ^ 4 * inverseRadius8 (12481 - 1) /
            envelopeGap 12481 (61 / 100) 161 (17 / (100 * 12481)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12481

namespace BstLean.Part266.Row12481
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12481 161 ≤ (4786397659 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12481 161 ≤ (1596823251 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (383797021 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12481 161 ≤ (965703849 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12481 161 ≤ (274831927 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12481 161 ≤ (502083787 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (502078087 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (502078087 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1609095727 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (36774863 / 6250000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3690623 / 1000000000) : ℝ) ≤ √(17 / (100 * 12481) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12481) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (140044369 / 62500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40113535459 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12481) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12481) ≤ (28327329 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12481) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12481 * (161 : ℝ) ^ 2 + 26 / (10 * 12481) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12481) : ℝ)) (tA 12481 * 161 ^ 2 + 26 / (10 * 12481)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3690623 / 1000000000))) * ((502078087 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3690623 / 1000000000)) ^ 3) * ((1609095727 / 1000000000000000000000000))) + ((36774863 / 6250000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3690623 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12481) : ℝ)) d.D d.V d.P (√(tA 12481) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3690623 / 1000000000)) ^ 2 * (((140044369 / 62500000000000)) * ((40113535459 / 1000000000000000000)))) + ((36774863 / 6250000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12481) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3690623 / 1000000000)) * ((502078087 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12481) : ℝ)) (tA 12481 * 161 ^ 2 + 26 / (10 * 12481)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((502078087 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3690623 / 1000000000)) ^ 2) * ((1609095727 / 1000000000000000000000000)) + ((36774863 / 6250000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12481) : ℝ)) (√(26 / (10 * 12481) : ℝ)) d.D d.V d.P (√(tA 12481) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3690623 / 1000000000)) * (((140044369 / 62500000000000)) * ((40113535459 / 1000000000000000000))) + ((36774863 / 6250000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12481) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((502078087 / 100000000000000000000) : ℝ) + ((36774863 / 6250000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12481

namespace BstLean.Part266.Row12481
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12481 161 ∧
    0 ≤ (tableEnvelope C).f1 12481 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12481 161 ∧
    0 ≤ (tableEnvelope C).w1 12481 161 ∧ 0 ≤ (tableEnvelope C).w2 12481 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12481 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12481 161 ∧ 0 ≤ d.f1 12481 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12481 161 ∧ 0 ≤ d.w1 12481 161 ∧ 0 ≤ d.w2 12481 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12481 ≤ 2 * (228 / 100 : ℝ) / 12481 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12481 ≤ 2 * (370 / 100 : ℝ) / 12481 := by
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
    (completeRAData (tableEnvelope C) 12481 161).locationBound 12481 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12481 161).energyBound 12481 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12481 161) (d.f1 12481 161) d.f2 ≤
      32 * (((4786397659 / 1000000000000000000) : ℝ) + (1596823251 / 1000000000000000000) + (383797021 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12481 161) (d.w1 12481 161)
      (d.w2 12481 161) ≤
      32 * (((965703849 / 50000000000000000000) : ℝ) + (274831927 / 20000000000000000000) + (502083787 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12481 161) (d.f1 12481 161) d.f2 ≤
      ((4786397659 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4786397659 / 1000000000000000000)) * ((1596823251 / 1000000000000000000)) * (126 / 100) +
      2 * (((1596823251 / 1000000000000000000)) ^ 2 + 2 * ((4786397659 / 1000000000000000000)) * ((383797021 / 1000000000000000000))) +
      6 * ((1596823251 / 1000000000000000000)) * ((383797021 / 1000000000000000000)) * (126 / 100) + 8 * ((383797021 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12481 161) (d.f1 12481 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12481 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12481 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12481 161) (d.f1 12481 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12481 161) (d.w1 12481 161) (d.w2 12481 161)
  have hwexpr0 : 0 ≤ d.w0 12481 161 + d.w1 12481 161 * √(π / 2) +
      2 * d.w2 12481 161 + energyR16 12481 *
      radiusPolynomialRoot16 (d.w0 12481 161) (d.w1 12481 161) (d.w2 12481 161) := by
    positivity
  constructor
  · change (12481 : ℝ) ^ 8 * (mA 12481 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12481 161) (d.f1 12481 161) d.f2 + locationR16 12481 *
        radiusPolynomialRoot16 (d.f0 12481 161) (d.f1 12481 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12481 : ℝ) ^ 8 * (mA 12481 : ℝ) ^ 8 *
        ((((4786397659 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4786397659 / 1000000000000000000)) * ((1596823251 / 1000000000000000000)) * (126 / 100) +
          2 * (((1596823251 / 1000000000000000000)) ^ 2 + 2 * ((4786397659 / 1000000000000000000)) * ((383797021 / 1000000000000000000))) +
          6 * ((1596823251 / 1000000000000000000)) * ((383797021 / 1000000000000000000)) * (126 / 100) + 8 * ((383797021 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12481) *
          (32 * (((4786397659 / 1000000000000000000) : ℝ) + (1596823251 / 1000000000000000000) + (383797021 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12481 : ℝ) ^ 16 *
      (d.w0 12481 161 + d.w1 12481 161 * √(π / 2) + 2 * d.w2 12481 161 +
        energyR16 12481 * radiusPolynomialRoot16 (d.w0 12481 161) (d.w1 12481 161)
          (d.w2 12481 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12481 : ℝ) ^ 16 *
        (((965703849 / 50000000000000000000) : ℝ) + ((274831927 / 20000000000000000000)) * (126 / 100) + 2 * ((502083787 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12481) *
          (32 * (((965703849 / 50000000000000000000) : ℝ) + (274831927 / 20000000000000000000) + (502083787 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12481

/-! A coarse bound on the actual paper statistics constant at dimension 12482. -/
namespace BstLean.Part266.Row12482
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12480 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12480 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12480 128 ≤ (12734 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12734 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12482) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12482 : ℕ))
    (by norm_num : (12482 : ℕ) ≤ 16384)
  have ht : paperTail256 12482 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12482 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12482 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12482 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12482 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12482 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12480 128 * √(2 / (12482 : ℝ)) *
      (√(12482 : ℝ) + paperT0 12482 + paperTail256 12482) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12482 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12482 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12482 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12480 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12480 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12482 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12482

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12482
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12482 (61 / 100) 161 (17 / (100 * 12482)) (26 / (10 * 12482)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12482 (61 / 100) 161 (17 / (100 * 12482)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (250978709 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (321716023 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5880170871 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12482 / 12482 * (61 / 100)) ^ 4 * inverseRadius8 (12482 - 1) /
            envelopeGap 12482 (61 / 100) 161 (17 / (100 * 12482)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12482

namespace BstLean.Part266.Row12482
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12482 161 ≤ (4785439591 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12482 161 ≤ (798251781 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (383720167 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12482 161 ≤ (1930943627 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12482 161 ≤ (343457357 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 12482 161 ≤ (100392623 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (250978709 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (250978709 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (321716023 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5880170871 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((147619 / 40000000) : ℝ) ≤ √(17 / (100 * 12482) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12482) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1120220311 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (10026777009 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12482) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12482) ≤ (56650119 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12482) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12482 * (161 : ℝ) ^ 2 + 26 / (10 * 12482) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12482) : ℝ)) (tA 12482 * 161 ^ 2 + 26 / (10 * 12482)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((147619 / 40000000))) * ((250978709 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((147619 / 40000000)) ^ 3) * ((321716023 / 200000000000000000000000))) + ((5880170871 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((147619 / 40000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12482) : ℝ)) d.D d.V d.P (√(tA 12482) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((147619 / 40000000)) ^ 2 * (((1120220311 / 500000000000000)) * ((10026777009 / 250000000000000000)))) + ((5880170871 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12482) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((147619 / 40000000)) * ((250978709 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12482) : ℝ)) (tA 12482 * 161 ^ 2 + 26 / (10 * 12482)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((250978709 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((147619 / 40000000)) ^ 2) * ((321716023 / 200000000000000000000000)) + ((5880170871 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12482) : ℝ)) (√(26 / (10 * 12482) : ℝ)) d.D d.V d.P (√(tA 12482) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((147619 / 40000000)) * (((1120220311 / 500000000000000)) * ((10026777009 / 250000000000000000))) + ((5880170871 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12482) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((250978709 / 50000000000000000000) : ℝ) + ((5880170871 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12482

namespace BstLean.Part266.Row12482
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12482 161 ∧
    0 ≤ (tableEnvelope C).f1 12482 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12482 161 ∧
    0 ≤ (tableEnvelope C).w1 12482 161 ∧ 0 ≤ (tableEnvelope C).w2 12482 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12482 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12482 161 ∧ 0 ≤ d.f1 12482 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12482 161 ∧ 0 ≤ d.w1 12482 161 ∧ 0 ≤ d.w2 12482 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12482 ≤ 2 * (228 / 100 : ℝ) / 12482 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12482 ≤ 2 * (370 / 100 : ℝ) / 12482 := by
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
    (completeRAData (tableEnvelope C) 12482 161).locationBound 12482 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12482 161).energyBound 12482 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12482 161) (d.f1 12482 161) d.f2 ≤
      32 * (((4785439591 / 1000000000000000000) : ℝ) + (798251781 / 500000000000000000) + (383720167 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12482 161) (d.w1 12482 161)
      (d.w2 12482 161) ≤
      32 * (((1930943627 / 100000000000000000000) : ℝ) + (343457357 / 25000000000000000000) + (100392623 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12482 161) (d.f1 12482 161) d.f2 ≤
      ((4785439591 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4785439591 / 1000000000000000000)) * ((798251781 / 500000000000000000)) * (126 / 100) +
      2 * (((798251781 / 500000000000000000)) ^ 2 + 2 * ((4785439591 / 1000000000000000000)) * ((383720167 / 1000000000000000000))) +
      6 * ((798251781 / 500000000000000000)) * ((383720167 / 1000000000000000000)) * (126 / 100) + 8 * ((383720167 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12482 161) (d.f1 12482 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12482 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12482 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12482 161) (d.f1 12482 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12482 161) (d.w1 12482 161) (d.w2 12482 161)
  have hwexpr0 : 0 ≤ d.w0 12482 161 + d.w1 12482 161 * √(π / 2) +
      2 * d.w2 12482 161 + energyR16 12482 *
      radiusPolynomialRoot16 (d.w0 12482 161) (d.w1 12482 161) (d.w2 12482 161) := by
    positivity
  constructor
  · change (12482 : ℝ) ^ 8 * (mA 12482 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12482 161) (d.f1 12482 161) d.f2 + locationR16 12482 *
        radiusPolynomialRoot16 (d.f0 12482 161) (d.f1 12482 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12482 : ℝ) ^ 8 * (mA 12482 : ℝ) ^ 8 *
        ((((4785439591 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4785439591 / 1000000000000000000)) * ((798251781 / 500000000000000000)) * (126 / 100) +
          2 * (((798251781 / 500000000000000000)) ^ 2 + 2 * ((4785439591 / 1000000000000000000)) * ((383720167 / 1000000000000000000))) +
          6 * ((798251781 / 500000000000000000)) * ((383720167 / 1000000000000000000)) * (126 / 100) + 8 * ((383720167 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12482) *
          (32 * (((4785439591 / 1000000000000000000) : ℝ) + (798251781 / 500000000000000000) + (383720167 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12482 : ℝ) ^ 16 *
      (d.w0 12482 161 + d.w1 12482 161 * √(π / 2) + 2 * d.w2 12482 161 +
        energyR16 12482 * radiusPolynomialRoot16 (d.w0 12482 161) (d.w1 12482 161)
          (d.w2 12482 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12482 : ℝ) ^ 16 *
        (((1930943627 / 100000000000000000000) : ℝ) + ((343457357 / 25000000000000000000)) * (126 / 100) + 2 * ((100392623 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12482) *
          (32 * (((1930943627 / 100000000000000000000) : ℝ) + (343457357 / 25000000000000000000) + (100392623 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12482

/-! A coarse bound on the actual paper statistics constant at dimension 12483. -/
namespace BstLean.Part266.Row12483
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12481 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12481 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12481 128 ≤ (12735 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12735 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12483) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12483 : ℕ))
    (by norm_num : (12483 : ℕ) ≤ 16384)
  have ht : paperTail256 12483 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12483 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12483 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12483 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12483 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12483 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12481 128 * √(2 / (12483 : ℝ)) *
      (√(12483 : ℝ) + paperT0 12483 + paperTail256 12483) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12483 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12483 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12483 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12481 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12481 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12483 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12483

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12483
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12483 (61 / 100) 161 (17 / (100 * 12483)) (26 / (10 * 12483)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12483 (61 / 100) 161 (17 / (100 * 12483)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (501836787 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (160806471 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1175273287 / 200000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12483 / 12483 * (61 / 100)) ^ 4 * inverseRadius8 (12483 - 1) /
            envelopeGap 12483 (61 / 100) 161 (17 / (100 * 12483)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12483

namespace BstLean.Part266.Row12483
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12483 161 ≤ (1196119529 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12483 161 ≤ (199522889 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (11988851 / 31250000000000000)
  w0 : (tableEnvelope C).w0 12483 161 ≤ (60327467 / 3125000000000000000)
  w1 : (tableEnvelope C).w1 12483 161 ≤ (686749481 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12483 161 ≤ (6273031 / 1250000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (501836787 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (501836787 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (160806471 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1175273287 / 200000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((461291 / 125000000) : ℝ) ≤ √(17 / (100 * 12483) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12483) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2240171393 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (10025170541 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12483) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12483) ≤ (113291161 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12483) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12483 * (161 : ℝ) ^ 2 + 26 / (10 * 12483) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12483) : ℝ)) (tA 12483 * 161 ^ 2 + 26 / (10 * 12483)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((461291 / 125000000))) * ((501836787 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((461291 / 125000000)) ^ 3) * ((160806471 / 100000000000000000000000))) + ((1175273287 / 200000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((461291 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12483) : ℝ)) d.D d.V d.P (√(tA 12483) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((461291 / 125000000)) ^ 2 * (((2240171393 / 1000000000000000)) * ((10025170541 / 250000000000000000)))) + ((1175273287 / 200000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12483) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((461291 / 125000000)) * ((501836787 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12483) : ℝ)) (tA 12483 * 161 ^ 2 + 26 / (10 * 12483)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((501836787 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((461291 / 125000000)) ^ 2) * ((160806471 / 100000000000000000000000)) + ((1175273287 / 200000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12483) : ℝ)) (√(26 / (10 * 12483) : ℝ)) d.D d.V d.P (√(tA 12483) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((461291 / 125000000)) * (((2240171393 / 1000000000000000)) * ((10025170541 / 250000000000000000))) + ((1175273287 / 200000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12483) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((501836787 / 100000000000000000000) : ℝ) + ((1175273287 / 200000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12483

namespace BstLean.Part266.Row12483
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12483 161 ∧
    0 ≤ (tableEnvelope C).f1 12483 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12483 161 ∧
    0 ≤ (tableEnvelope C).w1 12483 161 ∧ 0 ≤ (tableEnvelope C).w2 12483 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12483 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12483 161 ∧ 0 ≤ d.f1 12483 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12483 161 ∧ 0 ≤ d.w1 12483 161 ∧ 0 ≤ d.w2 12483 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12483 ≤ 2 * (228 / 100 : ℝ) / 12483 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12483 ≤ 2 * (370 / 100 : ℝ) / 12483 := by
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
    (completeRAData (tableEnvelope C) 12483 161).locationBound 12483 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12483 161).energyBound 12483 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12483 161) (d.f1 12483 161) d.f2 ≤
      32 * (((1196119529 / 250000000000000000) : ℝ) + (199522889 / 125000000000000000) + (11988851 / 31250000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12483 161) (d.w1 12483 161)
      (d.w2 12483 161) ≤
      32 * (((60327467 / 3125000000000000000) : ℝ) + (686749481 / 50000000000000000000) + (6273031 / 1250000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12483 161) (d.f1 12483 161) d.f2 ≤
      ((1196119529 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1196119529 / 250000000000000000)) * ((199522889 / 125000000000000000)) * (126 / 100) +
      2 * (((199522889 / 125000000000000000)) ^ 2 + 2 * ((1196119529 / 250000000000000000)) * ((11988851 / 31250000000000000))) +
      6 * ((199522889 / 125000000000000000)) * ((11988851 / 31250000000000000)) * (126 / 100) + 8 * ((11988851 / 31250000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12483 161) (d.f1 12483 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12483 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12483 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12483 161) (d.f1 12483 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12483 161) (d.w1 12483 161) (d.w2 12483 161)
  have hwexpr0 : 0 ≤ d.w0 12483 161 + d.w1 12483 161 * √(π / 2) +
      2 * d.w2 12483 161 + energyR16 12483 *
      radiusPolynomialRoot16 (d.w0 12483 161) (d.w1 12483 161) (d.w2 12483 161) := by
    positivity
  constructor
  · change (12483 : ℝ) ^ 8 * (mA 12483 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12483 161) (d.f1 12483 161) d.f2 + locationR16 12483 *
        radiusPolynomialRoot16 (d.f0 12483 161) (d.f1 12483 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12483 : ℝ) ^ 8 * (mA 12483 : ℝ) ^ 8 *
        ((((1196119529 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1196119529 / 250000000000000000)) * ((199522889 / 125000000000000000)) * (126 / 100) +
          2 * (((199522889 / 125000000000000000)) ^ 2 + 2 * ((1196119529 / 250000000000000000)) * ((11988851 / 31250000000000000))) +
          6 * ((199522889 / 125000000000000000)) * ((11988851 / 31250000000000000)) * (126 / 100) + 8 * ((11988851 / 31250000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12483) *
          (32 * (((1196119529 / 250000000000000000) : ℝ) + (199522889 / 125000000000000000) + (11988851 / 31250000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12483 : ℝ) ^ 16 *
      (d.w0 12483 161 + d.w1 12483 161 * √(π / 2) + 2 * d.w2 12483 161 +
        energyR16 12483 * radiusPolynomialRoot16 (d.w0 12483 161) (d.w1 12483 161)
          (d.w2 12483 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12483 : ℝ) ^ 16 *
        (((60327467 / 3125000000000000000) : ℝ) + ((686749481 / 50000000000000000000)) * (126 / 100) + 2 * ((6273031 / 1250000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12483) *
          (32 * (((60327467 / 3125000000000000000) : ℝ) + (686749481 / 50000000000000000000) + (6273031 / 1250000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12483

/-! A coarse bound on the actual paper statistics constant at dimension 12484. -/
namespace BstLean.Part266.Row12484
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12482 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12482 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12482 128 ≤ (12736 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12736 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12484) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12484 : ℕ))
    (by norm_num : (12484 : ℕ) ≤ 16384)
  have ht : paperTail256 12484 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12484 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12484 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12484 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12484 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12484 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12482 128 * √(2 / (12484 : ℝ)) *
      (√(12484 : ℝ) + paperT0 12484 + paperTail256 12484) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12484 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12484 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12484 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12482 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12482 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12484 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12484

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12484
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12484 (61 / 100) 161 (17 / (100 * 12484)) (26 / (10 * 12484)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12484 (61 / 100) 161 (17 / (100 * 12484)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (100343239 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1607549511 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5872564771 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12484 / 12484 * (61 / 100)) ^ 4 * inverseRadius8 (12484 - 1) /
            envelopeGap 12484 (61 / 100) 161 (17 / (100 * 12484)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12484

namespace BstLean.Part266.Row12484
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12484 161 ≤ (4783520719 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12484 161 ≤ (1595863633 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (15342657 / 40000000000000000)
  w0 : (tableEnvelope C).w0 12484 161 ≤ (965007599 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12484 161 ≤ (1373168981 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12484 161 ≤ (125430471 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (100343239 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (100343239 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1607549511 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5872564771 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((184509 / 50000000) : ℝ) ≤ √(17 / (100 * 12484) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12484) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2239902219 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40094257831 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12484) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12484) ≤ (113282087 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12484) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12484 * (161 : ℝ) ^ 2 + 26 / (10 * 12484) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12484) : ℝ)) (tA 12484 * 161 ^ 2 + 26 / (10 * 12484)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((184509 / 50000000))) * ((100343239 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((184509 / 50000000)) ^ 3) * ((1607549511 / 1000000000000000000000000))) + ((5872564771 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((184509 / 50000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12484) : ℝ)) d.D d.V d.P (√(tA 12484) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((184509 / 50000000)) ^ 2 * (((2239902219 / 1000000000000000)) * ((40094257831 / 1000000000000000000)))) + ((5872564771 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12484) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((184509 / 50000000)) * ((100343239 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12484) : ℝ)) (tA 12484 * 161 ^ 2 + 26 / (10 * 12484)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((100343239 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((184509 / 50000000)) ^ 2) * ((1607549511 / 1000000000000000000000000)) + ((5872564771 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12484) : ℝ)) (√(26 / (10 * 12484) : ℝ)) d.D d.V d.P (√(tA 12484) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((184509 / 50000000)) * (((2239902219 / 1000000000000000)) * ((40094257831 / 1000000000000000000))) + ((5872564771 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12484) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((100343239 / 20000000000000000000) : ℝ) + ((5872564771 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12484

namespace BstLean.Part266.Row12484
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12484 161 ∧
    0 ≤ (tableEnvelope C).f1 12484 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12484 161 ∧
    0 ≤ (tableEnvelope C).w1 12484 161 ∧ 0 ≤ (tableEnvelope C).w2 12484 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12484 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12484 161 ∧ 0 ≤ d.f1 12484 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12484 161 ∧ 0 ≤ d.w1 12484 161 ∧ 0 ≤ d.w2 12484 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12484 ≤ 2 * (228 / 100 : ℝ) / 12484 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12484 ≤ 2 * (370 / 100 : ℝ) / 12484 := by
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
    (completeRAData (tableEnvelope C) 12484 161).locationBound 12484 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12484 161).energyBound 12484 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12484 161) (d.f1 12484 161) d.f2 ≤
      32 * (((4783520719 / 1000000000000000000) : ℝ) + (1595863633 / 1000000000000000000) + (15342657 / 40000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12484 161) (d.w1 12484 161)
      (d.w2 12484 161) ≤
      32 * (((965007599 / 50000000000000000000) : ℝ) + (1373168981 / 100000000000000000000) + (125430471 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12484 161) (d.f1 12484 161) d.f2 ≤
      ((4783520719 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4783520719 / 1000000000000000000)) * ((1595863633 / 1000000000000000000)) * (126 / 100) +
      2 * (((1595863633 / 1000000000000000000)) ^ 2 + 2 * ((4783520719 / 1000000000000000000)) * ((15342657 / 40000000000000000))) +
      6 * ((1595863633 / 1000000000000000000)) * ((15342657 / 40000000000000000)) * (126 / 100) + 8 * ((15342657 / 40000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12484 161) (d.f1 12484 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12484 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12484 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12484 161) (d.f1 12484 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12484 161) (d.w1 12484 161) (d.w2 12484 161)
  have hwexpr0 : 0 ≤ d.w0 12484 161 + d.w1 12484 161 * √(π / 2) +
      2 * d.w2 12484 161 + energyR16 12484 *
      radiusPolynomialRoot16 (d.w0 12484 161) (d.w1 12484 161) (d.w2 12484 161) := by
    positivity
  constructor
  · change (12484 : ℝ) ^ 8 * (mA 12484 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12484 161) (d.f1 12484 161) d.f2 + locationR16 12484 *
        radiusPolynomialRoot16 (d.f0 12484 161) (d.f1 12484 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12484 : ℝ) ^ 8 * (mA 12484 : ℝ) ^ 8 *
        ((((4783520719 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4783520719 / 1000000000000000000)) * ((1595863633 / 1000000000000000000)) * (126 / 100) +
          2 * (((1595863633 / 1000000000000000000)) ^ 2 + 2 * ((4783520719 / 1000000000000000000)) * ((15342657 / 40000000000000000))) +
          6 * ((1595863633 / 1000000000000000000)) * ((15342657 / 40000000000000000)) * (126 / 100) + 8 * ((15342657 / 40000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12484) *
          (32 * (((4783520719 / 1000000000000000000) : ℝ) + (1595863633 / 1000000000000000000) + (15342657 / 40000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12484 : ℝ) ^ 16 *
      (d.w0 12484 161 + d.w1 12484 161 * √(π / 2) + 2 * d.w2 12484 161 +
        energyR16 12484 * radiusPolynomialRoot16 (d.w0 12484 161) (d.w1 12484 161)
          (d.w2 12484 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12484 : ℝ) ^ 16 *
        (((965007599 / 50000000000000000000) : ℝ) + ((1373168981 / 100000000000000000000)) * (126 / 100) + 2 * ((125430471 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12484) *
          (32 * (((965007599 / 50000000000000000000) : ℝ) + (1373168981 / 100000000000000000000) + (125430471 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12484

/-! A coarse bound on the actual paper statistics constant at dimension 12485. -/
namespace BstLean.Part266.Row12485
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12483 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12483 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12483 128 ≤ (12737 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12737 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12485) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12485 : ℕ))
    (by norm_num : (12485 : ℕ) ≤ 16384)
  have ht : paperTail256 12485 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12485 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12485 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12485 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12485 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12485 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12483 128 * √(2 / (12485 : ℝ)) *
      (√(12485 : ℝ) + paperT0 12485 + paperTail256 12485) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12485 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12485 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12485 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12483 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12483 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12485 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12485

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12485
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12485 (61 / 100) 161 (17 / (100 * 12485)) (26 / (10 * 12485)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12485 (61 / 100) 161 (17 / (100 * 12485)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (250797821 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1607034519 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5868765877 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12485 / 12485 * (61 / 100)) ^ 4 * inverseRadius8 (12485 - 1) /
            envelopeGap 12485 (61 / 100) 161 (17 / (100 * 12485)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12485

namespace BstLean.Part266.Row12485
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12485 161 ≤ (2391281829 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12485 161 ≤ (79777213 / 50000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (191744821 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12485 161 ≤ (385910323 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 12485 161 ≤ (1372839113 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12485 161 ≤ (31350083 / 6250000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (250797821 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (250797821 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1607034519 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5868765877 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((230627 / 62500000) : ℝ) ≤ √(17 / (100 * 12485) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12485) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (22396331 / 10000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40087835051 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12485) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12485) ≤ (113273013 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12485) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12485 * (161 : ℝ) ^ 2 + 26 / (10 * 12485) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12485) : ℝ)) (tA 12485 * 161 ^ 2 + 26 / (10 * 12485)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((230627 / 62500000))) * ((250797821 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((230627 / 62500000)) ^ 3) * ((1607034519 / 1000000000000000000000000))) + ((5868765877 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((230627 / 62500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12485) : ℝ)) d.D d.V d.P (√(tA 12485) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((230627 / 62500000)) ^ 2 * (((22396331 / 10000000000000)) * ((40087835051 / 1000000000000000000)))) + ((5868765877 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12485) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((230627 / 62500000)) * ((250797821 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12485) : ℝ)) (tA 12485 * 161 ^ 2 + 26 / (10 * 12485)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((250797821 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((230627 / 62500000)) ^ 2) * ((1607034519 / 1000000000000000000000000)) + ((5868765877 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12485) : ℝ)) (√(26 / (10 * 12485) : ℝ)) d.D d.V d.P (√(tA 12485) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((230627 / 62500000)) * (((22396331 / 10000000000000)) * ((40087835051 / 1000000000000000000))) + ((5868765877 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12485) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((250797821 / 50000000000000000000) : ℝ) + ((5868765877 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12485

namespace BstLean.Part266.Row12485
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12485 161 ∧
    0 ≤ (tableEnvelope C).f1 12485 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12485 161 ∧
    0 ≤ (tableEnvelope C).w1 12485 161 ∧ 0 ≤ (tableEnvelope C).w2 12485 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12485 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12485 161 ∧ 0 ≤ d.f1 12485 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12485 161 ∧ 0 ≤ d.w1 12485 161 ∧ 0 ≤ d.w2 12485 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12485 ≤ 2 * (228 / 100 : ℝ) / 12485 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12485 ≤ 2 * (370 / 100 : ℝ) / 12485 := by
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
    (completeRAData (tableEnvelope C) 12485 161).locationBound 12485 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12485 161).energyBound 12485 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12485 161) (d.f1 12485 161) d.f2 ≤
      32 * (((2391281829 / 500000000000000000) : ℝ) + (79777213 / 50000000000000000) + (191744821 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12485 161) (d.w1 12485 161)
      (d.w2 12485 161) ≤
      32 * (((385910323 / 20000000000000000000) : ℝ) + (1372839113 / 100000000000000000000) + (31350083 / 6250000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12485 161) (d.f1 12485 161) d.f2 ≤
      ((2391281829 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2391281829 / 500000000000000000)) * ((79777213 / 50000000000000000)) * (126 / 100) +
      2 * (((79777213 / 50000000000000000)) ^ 2 + 2 * ((2391281829 / 500000000000000000)) * ((191744821 / 500000000000000000))) +
      6 * ((79777213 / 50000000000000000)) * ((191744821 / 500000000000000000)) * (126 / 100) + 8 * ((191744821 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12485 161) (d.f1 12485 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12485 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12485 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12485 161) (d.f1 12485 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12485 161) (d.w1 12485 161) (d.w2 12485 161)
  have hwexpr0 : 0 ≤ d.w0 12485 161 + d.w1 12485 161 * √(π / 2) +
      2 * d.w2 12485 161 + energyR16 12485 *
      radiusPolynomialRoot16 (d.w0 12485 161) (d.w1 12485 161) (d.w2 12485 161) := by
    positivity
  constructor
  · change (12485 : ℝ) ^ 8 * (mA 12485 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12485 161) (d.f1 12485 161) d.f2 + locationR16 12485 *
        radiusPolynomialRoot16 (d.f0 12485 161) (d.f1 12485 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12485 : ℝ) ^ 8 * (mA 12485 : ℝ) ^ 8 *
        ((((2391281829 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2391281829 / 500000000000000000)) * ((79777213 / 50000000000000000)) * (126 / 100) +
          2 * (((79777213 / 50000000000000000)) ^ 2 + 2 * ((2391281829 / 500000000000000000)) * ((191744821 / 500000000000000000))) +
          6 * ((79777213 / 50000000000000000)) * ((191744821 / 500000000000000000)) * (126 / 100) + 8 * ((191744821 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12485) *
          (32 * (((2391281829 / 500000000000000000) : ℝ) + (79777213 / 50000000000000000) + (191744821 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12485 : ℝ) ^ 16 *
      (d.w0 12485 161 + d.w1 12485 161 * √(π / 2) + 2 * d.w2 12485 161 +
        energyR16 12485 * radiusPolynomialRoot16 (d.w0 12485 161) (d.w1 12485 161)
          (d.w2 12485 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12485 : ℝ) ^ 16 *
        (((385910323 / 20000000000000000000) : ℝ) + ((1372839113 / 100000000000000000000)) * (126 / 100) + 2 * ((31350083 / 6250000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12485) *
          (32 * (((385910323 / 20000000000000000000) : ℝ) + (1372839113 / 100000000000000000000) + (31350083 / 6250000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12485

/-! A coarse bound on the actual paper statistics constant at dimension 12486. -/
namespace BstLean.Part266.Row12486
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12484 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12484 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12484 128 ≤ (12738 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12738 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12486) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12486 : ℕ))
    (by norm_num : (12486 : ℕ) ≤ 16384)
  have ht : paperTail256 12486 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12486 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12486 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12486 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12486 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12486 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12484 128 * √(2 / (12486 : ℝ)) *
      (√(12486 : ℝ) + paperT0 12486 + paperTail256 12486) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12486 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12486 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12486 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12484 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12484 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12486 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12486

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12486
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12486 (61 / 100) 161 (17 / (100 * 12486)) (26 / (10 * 12486)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12486 (61 / 100) 161 (17 / (100 * 12486)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (501475127 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (401629933 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (23459879 / 4000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12486 / 12486 * (61 / 100)) ^ 4 * inverseRadius8 (12486 - 1) /
            envelopeGap 12486 (61 / 100) 161 (17 / (100 * 12486)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12486

namespace BstLean.Part266.Row12486
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12486 161 ≤ (298850433 / 62500000000000000)
  f1 : (tableEnvelope C).f1 12486 161 ≤ (159522499 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (383412881 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12486 161 ≤ (1929088193 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12486 161 ≤ (274501871 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12486 161 ≤ (501480809 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (501475127 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (501475127 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (401629933 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (23459879 / 4000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((922471 / 250000000) : ℝ) ≤ √(17 / (100 * 12486) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12486) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2239364033 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (20040706899 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12486) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12486) ≤ (113263941 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12486) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12486 * (161 : ℝ) ^ 2 + 26 / (10 * 12486) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12486) : ℝ)) (tA 12486 * 161 ^ 2 + 26 / (10 * 12486)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((922471 / 250000000))) * ((501475127 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((922471 / 250000000)) ^ 3) * ((401629933 / 250000000000000000000000))) + ((23459879 / 4000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((922471 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12486) : ℝ)) d.D d.V d.P (√(tA 12486) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((922471 / 250000000)) ^ 2 * (((2239364033 / 1000000000000000)) * ((20040706899 / 500000000000000000)))) + ((23459879 / 4000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12486) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((922471 / 250000000)) * ((501475127 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12486) : ℝ)) (tA 12486 * 161 ^ 2 + 26 / (10 * 12486)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((501475127 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((922471 / 250000000)) ^ 2) * ((401629933 / 250000000000000000000000)) + ((23459879 / 4000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12486) : ℝ)) (√(26 / (10 * 12486) : ℝ)) d.D d.V d.P (√(tA 12486) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((922471 / 250000000)) * (((2239364033 / 1000000000000000)) * ((20040706899 / 500000000000000000))) + ((23459879 / 4000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12486) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((501475127 / 100000000000000000000) : ℝ) + ((23459879 / 4000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12486

namespace BstLean.Part266.Row12486
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12486 161 ∧
    0 ≤ (tableEnvelope C).f1 12486 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12486 161 ∧
    0 ≤ (tableEnvelope C).w1 12486 161 ∧ 0 ≤ (tableEnvelope C).w2 12486 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12486 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12486 161 ∧ 0 ≤ d.f1 12486 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12486 161 ∧ 0 ≤ d.w1 12486 161 ∧ 0 ≤ d.w2 12486 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12486 ≤ 2 * (228 / 100 : ℝ) / 12486 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12486 ≤ 2 * (370 / 100 : ℝ) / 12486 := by
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
    (completeRAData (tableEnvelope C) 12486 161).locationBound 12486 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12486 161).energyBound 12486 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12486 161) (d.f1 12486 161) d.f2 ≤
      32 * (((298850433 / 62500000000000000) : ℝ) + (159522499 / 100000000000000000) + (383412881 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12486 161) (d.w1 12486 161)
      (d.w2 12486 161) ≤
      32 * (((1929088193 / 100000000000000000000) : ℝ) + (274501871 / 20000000000000000000) + (501480809 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12486 161) (d.f1 12486 161) d.f2 ≤
      ((298850433 / 62500000000000000) : ℝ) ^ 2 + 2 * ((298850433 / 62500000000000000)) * ((159522499 / 100000000000000000)) * (126 / 100) +
      2 * (((159522499 / 100000000000000000)) ^ 2 + 2 * ((298850433 / 62500000000000000)) * ((383412881 / 1000000000000000000))) +
      6 * ((159522499 / 100000000000000000)) * ((383412881 / 1000000000000000000)) * (126 / 100) + 8 * ((383412881 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12486 161) (d.f1 12486 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12486 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12486 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12486 161) (d.f1 12486 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12486 161) (d.w1 12486 161) (d.w2 12486 161)
  have hwexpr0 : 0 ≤ d.w0 12486 161 + d.w1 12486 161 * √(π / 2) +
      2 * d.w2 12486 161 + energyR16 12486 *
      radiusPolynomialRoot16 (d.w0 12486 161) (d.w1 12486 161) (d.w2 12486 161) := by
    positivity
  constructor
  · change (12486 : ℝ) ^ 8 * (mA 12486 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12486 161) (d.f1 12486 161) d.f2 + locationR16 12486 *
        radiusPolynomialRoot16 (d.f0 12486 161) (d.f1 12486 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12486 : ℝ) ^ 8 * (mA 12486 : ℝ) ^ 8 *
        ((((298850433 / 62500000000000000) : ℝ) ^ 2 + 2 * ((298850433 / 62500000000000000)) * ((159522499 / 100000000000000000)) * (126 / 100) +
          2 * (((159522499 / 100000000000000000)) ^ 2 + 2 * ((298850433 / 62500000000000000)) * ((383412881 / 1000000000000000000))) +
          6 * ((159522499 / 100000000000000000)) * ((383412881 / 1000000000000000000)) * (126 / 100) + 8 * ((383412881 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12486) *
          (32 * (((298850433 / 62500000000000000) : ℝ) + (159522499 / 100000000000000000) + (383412881 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12486 : ℝ) ^ 16 *
      (d.w0 12486 161 + d.w1 12486 161 * √(π / 2) + 2 * d.w2 12486 161 +
        energyR16 12486 * radiusPolynomialRoot16 (d.w0 12486 161) (d.w1 12486 161)
          (d.w2 12486 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12486 : ℝ) ^ 16 *
        (((1929088193 / 100000000000000000000) : ℝ) + ((274501871 / 20000000000000000000)) * (126 / 100) + 2 * ((501480809 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12486) *
          (32 * (((1929088193 / 100000000000000000000) : ℝ) + (274501871 / 20000000000000000000) + (501480809 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12486

/-! A coarse bound on the actual paper statistics constant at dimension 12487. -/
namespace BstLean.Part266.Row12487
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12485 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12485 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12485 128 ≤ (12739 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12739 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12487) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12487 : ℕ))
    (by norm_num : (12487 : ℕ) ≤ 16384)
  have ht : paperTail256 12487 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12487 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12487 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12487 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12487 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12487 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12485 128 * √(2 / (12487 : ℝ)) *
      (√(12487 : ℝ) + paperT0 12487 + paperTail256 12487) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12487 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12487 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12487 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12485 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12485 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12487 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12487

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12487
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12487 (61 / 100) 161 (17 / (100 * 12487)) (26 / (10 * 12487)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12487 (61 / 100) 161 (17 / (100 * 12487)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (501354651 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (50187661 / 31250000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1465294097 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12487 / 12487 * (61 / 100)) ^ 4 * inverseRadius8 (12487 - 1) /
            envelopeGap 12487 (61 / 100) 161 (17 / (100 * 12487)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12487

namespace BstLean.Part266.Row12487
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12487 161 ≤ (597581317 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12487 161 ≤ (1594905827 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (23958509 / 62500000000000000)
  w0 : (tableEnvelope C).w0 12487 161 ≤ (964312467 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12487 161 ≤ (1372179711 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12487 161 ≤ (501360329 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (501354651 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (501354651 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (50187661 / 31250000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1465294097 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((461217 / 125000000) : ℝ) ≤ √(17 / (100 * 12487) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12487) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2239095021 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40074994099 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12487) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12487) ≤ (113254871 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12487) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12487 * (161 : ℝ) ^ 2 + 26 / (10 * 12487) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12487) : ℝ)) (tA 12487 * 161 ^ 2 + 26 / (10 * 12487)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((461217 / 125000000))) * ((501354651 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((461217 / 125000000)) ^ 3) * ((50187661 / 31250000000000000000000))) + ((1465294097 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((461217 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12487) : ℝ)) d.D d.V d.P (√(tA 12487) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((461217 / 125000000)) ^ 2 * (((2239095021 / 1000000000000000)) * ((40074994099 / 1000000000000000000)))) + ((1465294097 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12487) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((461217 / 125000000)) * ((501354651 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12487) : ℝ)) (tA 12487 * 161 ^ 2 + 26 / (10 * 12487)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((501354651 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((461217 / 125000000)) ^ 2) * ((50187661 / 31250000000000000000000)) + ((1465294097 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12487) : ℝ)) (√(26 / (10 * 12487) : ℝ)) d.D d.V d.P (√(tA 12487) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((461217 / 125000000)) * (((2239095021 / 1000000000000000)) * ((40074994099 / 1000000000000000000))) + ((1465294097 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12487) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((501354651 / 100000000000000000000) : ℝ) + ((1465294097 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12487

namespace BstLean.Part266.Row12487
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12487 161 ∧
    0 ≤ (tableEnvelope C).f1 12487 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12487 161 ∧
    0 ≤ (tableEnvelope C).w1 12487 161 ∧ 0 ≤ (tableEnvelope C).w2 12487 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12487 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12487 161 ∧ 0 ≤ d.f1 12487 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12487 161 ∧ 0 ≤ d.w1 12487 161 ∧ 0 ≤ d.w2 12487 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12487 ≤ 2 * (228 / 100 : ℝ) / 12487 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12487 ≤ 2 * (370 / 100 : ℝ) / 12487 := by
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
    (completeRAData (tableEnvelope C) 12487 161).locationBound 12487 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12487 161).energyBound 12487 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12487 161) (d.f1 12487 161) d.f2 ≤
      32 * (((597581317 / 125000000000000000) : ℝ) + (1594905827 / 1000000000000000000) + (23958509 / 62500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12487 161) (d.w1 12487 161)
      (d.w2 12487 161) ≤
      32 * (((964312467 / 50000000000000000000) : ℝ) + (1372179711 / 100000000000000000000) + (501360329 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12487 161) (d.f1 12487 161) d.f2 ≤
      ((597581317 / 125000000000000000) : ℝ) ^ 2 + 2 * ((597581317 / 125000000000000000)) * ((1594905827 / 1000000000000000000)) * (126 / 100) +
      2 * (((1594905827 / 1000000000000000000)) ^ 2 + 2 * ((597581317 / 125000000000000000)) * ((23958509 / 62500000000000000))) +
      6 * ((1594905827 / 1000000000000000000)) * ((23958509 / 62500000000000000)) * (126 / 100) + 8 * ((23958509 / 62500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12487 161) (d.f1 12487 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12487 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12487 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12487 161) (d.f1 12487 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12487 161) (d.w1 12487 161) (d.w2 12487 161)
  have hwexpr0 : 0 ≤ d.w0 12487 161 + d.w1 12487 161 * √(π / 2) +
      2 * d.w2 12487 161 + energyR16 12487 *
      radiusPolynomialRoot16 (d.w0 12487 161) (d.w1 12487 161) (d.w2 12487 161) := by
    positivity
  constructor
  · change (12487 : ℝ) ^ 8 * (mA 12487 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12487 161) (d.f1 12487 161) d.f2 + locationR16 12487 *
        radiusPolynomialRoot16 (d.f0 12487 161) (d.f1 12487 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12487 : ℝ) ^ 8 * (mA 12487 : ℝ) ^ 8 *
        ((((597581317 / 125000000000000000) : ℝ) ^ 2 + 2 * ((597581317 / 125000000000000000)) * ((1594905827 / 1000000000000000000)) * (126 / 100) +
          2 * (((1594905827 / 1000000000000000000)) ^ 2 + 2 * ((597581317 / 125000000000000000)) * ((23958509 / 62500000000000000))) +
          6 * ((1594905827 / 1000000000000000000)) * ((23958509 / 62500000000000000)) * (126 / 100) + 8 * ((23958509 / 62500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12487) *
          (32 * (((597581317 / 125000000000000000) : ℝ) + (1594905827 / 1000000000000000000) + (23958509 / 62500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12487 : ℝ) ^ 16 *
      (d.w0 12487 161 + d.w1 12487 161 * √(π / 2) + 2 * d.w2 12487 161 +
        energyR16 12487 * radiusPolynomialRoot16 (d.w0 12487 161) (d.w1 12487 161)
          (d.w2 12487 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12487 : ℝ) ^ 16 *
        (((964312467 / 50000000000000000000) : ℝ) + ((1372179711 / 100000000000000000000)) * (126 / 100) + 2 * ((501360329 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12487) *
          (32 * (((964312467 / 50000000000000000000) : ℝ) + (1372179711 / 100000000000000000000) + (501360329 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12487

/-! A coarse bound on the actual paper statistics constant at dimension 12488. -/
namespace BstLean.Part266.Row12488
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12486 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12486 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12486 128 ≤ (12740 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12740 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12488) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12488 : ℕ))
    (by norm_num : (12488 : ℕ) ≤ 16384)
  have ht : paperTail256 12488 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12488 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12488 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12488 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12488 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12488 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12486 128 * √(2 / (12488 : ℝ)) *
      (√(12488 : ℝ) + paperT0 12488 + paperTail256 12488) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12488 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12488 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12488 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12486 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12486 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12488 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12488

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12488
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12488 (61 / 100) 161 (17 / (100 * 12488)) (26 / (10 * 12488)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12488 (61 / 100) 161 (17 / (100 * 12488)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (501234213 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1605490777 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5857385789 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12488 / 12488 * (61 / 100)) ^ 4 * inverseRadius8 (12488 - 1) /
            envelopeGap 12488 (61 / 100) 161 (17 / (100 * 12488)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12488

namespace BstLean.Part266.Row12488
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12488 161 ≤ (955938147 / 200000000000000000)
  f1 : (tableEnvelope C).f1 12488 161 ≤ (1594585901 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (191629663 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12488 161 ≤ (964080531 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12488 161 ≤ (685924903 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12488 161 ≤ (501239887 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (501234213 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (501234213 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1605490777 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5857385789 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3689589 / 1000000000) : ℝ) ≤ √(17 / (100 * 12488) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12488) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2238826061 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4006857593 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12488) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12488) ≤ (113245801 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12488) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12488 * (161 : ℝ) ^ 2 + 26 / (10 * 12488) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12488) : ℝ)) (tA 12488 * 161 ^ 2 + 26 / (10 * 12488)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3689589 / 1000000000))) * ((501234213 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3689589 / 1000000000)) ^ 3) * ((1605490777 / 1000000000000000000000000))) + ((5857385789 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3689589 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12488) : ℝ)) d.D d.V d.P (√(tA 12488) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3689589 / 1000000000)) ^ 2 * (((2238826061 / 1000000000000000)) * ((4006857593 / 100000000000000000)))) + ((5857385789 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12488) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3689589 / 1000000000)) * ((501234213 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12488) : ℝ)) (tA 12488 * 161 ^ 2 + 26 / (10 * 12488)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((501234213 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3689589 / 1000000000)) ^ 2) * ((1605490777 / 1000000000000000000000000)) + ((5857385789 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12488) : ℝ)) (√(26 / (10 * 12488) : ℝ)) d.D d.V d.P (√(tA 12488) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3689589 / 1000000000)) * (((2238826061 / 1000000000000000)) * ((4006857593 / 100000000000000000))) + ((5857385789 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12488) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((501234213 / 100000000000000000000) : ℝ) + ((5857385789 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12488

namespace BstLean.Part266.Row12488
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12488 161 ∧
    0 ≤ (tableEnvelope C).f1 12488 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12488 161 ∧
    0 ≤ (tableEnvelope C).w1 12488 161 ∧ 0 ≤ (tableEnvelope C).w2 12488 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12488 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12488 161 ∧ 0 ≤ d.f1 12488 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12488 161 ∧ 0 ≤ d.w1 12488 161 ∧ 0 ≤ d.w2 12488 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12488 ≤ 2 * (228 / 100 : ℝ) / 12488 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12488 ≤ 2 * (370 / 100 : ℝ) / 12488 := by
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
    (completeRAData (tableEnvelope C) 12488 161).locationBound 12488 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12488 161).energyBound 12488 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12488 161) (d.f1 12488 161) d.f2 ≤
      32 * (((955938147 / 200000000000000000) : ℝ) + (1594585901 / 1000000000000000000) + (191629663 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12488 161) (d.w1 12488 161)
      (d.w2 12488 161) ≤
      32 * (((964080531 / 50000000000000000000) : ℝ) + (685924903 / 50000000000000000000) + (501239887 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12488 161) (d.f1 12488 161) d.f2 ≤
      ((955938147 / 200000000000000000) : ℝ) ^ 2 + 2 * ((955938147 / 200000000000000000)) * ((1594585901 / 1000000000000000000)) * (126 / 100) +
      2 * (((1594585901 / 1000000000000000000)) ^ 2 + 2 * ((955938147 / 200000000000000000)) * ((191629663 / 500000000000000000))) +
      6 * ((1594585901 / 1000000000000000000)) * ((191629663 / 500000000000000000)) * (126 / 100) + 8 * ((191629663 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12488 161) (d.f1 12488 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12488 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12488 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12488 161) (d.f1 12488 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12488 161) (d.w1 12488 161) (d.w2 12488 161)
  have hwexpr0 : 0 ≤ d.w0 12488 161 + d.w1 12488 161 * √(π / 2) +
      2 * d.w2 12488 161 + energyR16 12488 *
      radiusPolynomialRoot16 (d.w0 12488 161) (d.w1 12488 161) (d.w2 12488 161) := by
    positivity
  constructor
  · change (12488 : ℝ) ^ 8 * (mA 12488 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12488 161) (d.f1 12488 161) d.f2 + locationR16 12488 *
        radiusPolynomialRoot16 (d.f0 12488 161) (d.f1 12488 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12488 : ℝ) ^ 8 * (mA 12488 : ℝ) ^ 8 *
        ((((955938147 / 200000000000000000) : ℝ) ^ 2 + 2 * ((955938147 / 200000000000000000)) * ((1594585901 / 1000000000000000000)) * (126 / 100) +
          2 * (((1594585901 / 1000000000000000000)) ^ 2 + 2 * ((955938147 / 200000000000000000)) * ((191629663 / 500000000000000000))) +
          6 * ((1594585901 / 1000000000000000000)) * ((191629663 / 500000000000000000)) * (126 / 100) + 8 * ((191629663 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12488) *
          (32 * (((955938147 / 200000000000000000) : ℝ) + (1594585901 / 1000000000000000000) + (191629663 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12488 : ℝ) ^ 16 *
      (d.w0 12488 161 + d.w1 12488 161 * √(π / 2) + 2 * d.w2 12488 161 +
        energyR16 12488 * radiusPolynomialRoot16 (d.w0 12488 161) (d.w1 12488 161)
          (d.w2 12488 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12488 : ℝ) ^ 16 *
        (((964080531 / 50000000000000000000) : ℝ) + ((685924903 / 50000000000000000000)) * (126 / 100) + 2 * ((501239887 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12488) *
          (32 * (((964080531 / 50000000000000000000) : ℝ) + (685924903 / 50000000000000000000) + (501239887 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12488

/-! A coarse bound on the actual paper statistics constant at dimension 12489. -/
namespace BstLean.Part266.Row12489
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12487 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12487 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12487 128 ≤ (12741 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12741 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12489) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12489 : ℕ))
    (by norm_num : (12489 : ℕ) ≤ 16384)
  have ht : paperTail256 12489 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12489 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12489 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12489 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12489 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12489 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12487 128 * √(2 / (12489 : ℝ)) *
      (√(12489 : ℝ) + paperT0 12489 + paperTail256 12489) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12489 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12489 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12489 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12487 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12487 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12489 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12489

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12489
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12489 (61 / 100) 161 (17 / (100 * 12489)) (26 / (10 * 12489)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12489 (61 / 100) 161 (17 / (100 * 12489)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (250556907 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1604976609 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5853597951 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12489 / 12489 * (61 / 100)) ^ 4 * inverseRadius8 (12489 - 1) /
            envelopeGap 12489 (61 / 100) 161 (17 / (100 * 12489)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12489

namespace BstLean.Part266.Row12489
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12489 161 ≤ (1194683753 / 250000000000000000)
  f1 : (tableEnvelope C).f1 12489 161 ≤ (1594266947 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (95795659 / 250000000000000000)
  w0 : (tableEnvelope C).w0 12489 161 ≤ (1927698127 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12489 161 ≤ (685760193 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12489 161 ≤ (100223897 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (250556907 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (250556907 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1604976609 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5853597951 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3689441 / 1000000000) : ℝ) ≤ √(17 / (100 * 12489) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12489) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (559639289 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (10015539829 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12489) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12489) ≤ (56618367 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12489) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12489 * (161 : ℝ) ^ 2 + 26 / (10 * 12489) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12489) : ℝ)) (tA 12489 * 161 ^ 2 + 26 / (10 * 12489)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3689441 / 1000000000))) * ((250556907 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3689441 / 1000000000)) ^ 3) * ((1604976609 / 1000000000000000000000000))) + ((5853597951 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3689441 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12489) : ℝ)) d.D d.V d.P (√(tA 12489) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3689441 / 1000000000)) ^ 2 * (((559639289 / 250000000000000)) * ((10015539829 / 250000000000000000)))) + ((5853597951 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12489) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3689441 / 1000000000)) * ((250556907 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12489) : ℝ)) (tA 12489 * 161 ^ 2 + 26 / (10 * 12489)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((250556907 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3689441 / 1000000000)) ^ 2) * ((1604976609 / 1000000000000000000000000)) + ((5853597951 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12489) : ℝ)) (√(26 / (10 * 12489) : ℝ)) d.D d.V d.P (√(tA 12489) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3689441 / 1000000000)) * (((559639289 / 250000000000000)) * ((10015539829 / 250000000000000000))) + ((5853597951 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12489) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((250556907 / 50000000000000000000) : ℝ) + ((5853597951 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12489

namespace BstLean.Part266.Row12489
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12489 161 ∧
    0 ≤ (tableEnvelope C).f1 12489 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12489 161 ∧
    0 ≤ (tableEnvelope C).w1 12489 161 ∧ 0 ≤ (tableEnvelope C).w2 12489 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12489 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12489 161 ∧ 0 ≤ d.f1 12489 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12489 161 ∧ 0 ≤ d.w1 12489 161 ∧ 0 ≤ d.w2 12489 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12489 ≤ 2 * (228 / 100 : ℝ) / 12489 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12489 ≤ 2 * (370 / 100 : ℝ) / 12489 := by
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
    (completeRAData (tableEnvelope C) 12489 161).locationBound 12489 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12489 161).energyBound 12489 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12489 161) (d.f1 12489 161) d.f2 ≤
      32 * (((1194683753 / 250000000000000000) : ℝ) + (1594266947 / 1000000000000000000) + (95795659 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12489 161) (d.w1 12489 161)
      (d.w2 12489 161) ≤
      32 * (((1927698127 / 100000000000000000000) : ℝ) + (685760193 / 50000000000000000000) + (100223897 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12489 161) (d.f1 12489 161) d.f2 ≤
      ((1194683753 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1194683753 / 250000000000000000)) * ((1594266947 / 1000000000000000000)) * (126 / 100) +
      2 * (((1594266947 / 1000000000000000000)) ^ 2 + 2 * ((1194683753 / 250000000000000000)) * ((95795659 / 250000000000000000))) +
      6 * ((1594266947 / 1000000000000000000)) * ((95795659 / 250000000000000000)) * (126 / 100) + 8 * ((95795659 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12489 161) (d.f1 12489 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12489 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12489 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12489 161) (d.f1 12489 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12489 161) (d.w1 12489 161) (d.w2 12489 161)
  have hwexpr0 : 0 ≤ d.w0 12489 161 + d.w1 12489 161 * √(π / 2) +
      2 * d.w2 12489 161 + energyR16 12489 *
      radiusPolynomialRoot16 (d.w0 12489 161) (d.w1 12489 161) (d.w2 12489 161) := by
    positivity
  constructor
  · change (12489 : ℝ) ^ 8 * (mA 12489 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12489 161) (d.f1 12489 161) d.f2 + locationR16 12489 *
        radiusPolynomialRoot16 (d.f0 12489 161) (d.f1 12489 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12489 : ℝ) ^ 8 * (mA 12489 : ℝ) ^ 8 *
        ((((1194683753 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1194683753 / 250000000000000000)) * ((1594266947 / 1000000000000000000)) * (126 / 100) +
          2 * (((1594266947 / 1000000000000000000)) ^ 2 + 2 * ((1194683753 / 250000000000000000)) * ((95795659 / 250000000000000000))) +
          6 * ((1594266947 / 1000000000000000000)) * ((95795659 / 250000000000000000)) * (126 / 100) + 8 * ((95795659 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12489) *
          (32 * (((1194683753 / 250000000000000000) : ℝ) + (1594266947 / 1000000000000000000) + (95795659 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12489 : ℝ) ^ 16 *
      (d.w0 12489 161 + d.w1 12489 161 * √(π / 2) + 2 * d.w2 12489 161 +
        energyR16 12489 * radiusPolynomialRoot16 (d.w0 12489 161) (d.w1 12489 161)
          (d.w2 12489 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12489 : ℝ) ^ 16 *
        (((1927698127 / 100000000000000000000) : ℝ) + ((685760193 / 50000000000000000000)) * (126 / 100) + 2 * ((100223897 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12489) *
          (32 * (((1927698127 / 100000000000000000000) : ℝ) + (685760193 / 50000000000000000000) + (100223897 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12489

/-! A coarse bound on the actual paper statistics constant at dimension 12490. -/
namespace BstLean.Part266.Row12490
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12488 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12488 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12488 128 ≤ (12742 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12742 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12490) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12490 : ℕ))
    (by norm_num : (12490 : ℕ) ≤ 16384)
  have ht : paperTail256 12490 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12490 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12490 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12490 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12490 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12490 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12488 128 * √(2 / (12490 : ℝ)) *
      (√(12490 : ℝ) + paperT0 12490 + paperTail256 12490) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12490 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12490 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12490 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12488 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12488 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12490 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12490

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12490
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12490 (61 / 100) 161 (17 / (100 * 12490)) (26 / (10 * 12490)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12490 (61 / 100) 161 (17 / (100 * 12490)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (250496727 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1604462647 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5849812871 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12490 / 12490 * (61 / 100)) ^ 4 * inverseRadius8 (12490 - 1) /
            envelopeGap 12490 (61 / 100) 161 (17 / (100 * 12490)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12490

namespace BstLean.Part266.Row12490
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12490 161 ≤ (597222453 / 125000000000000000)
  f1 : (tableEnvelope C).f1 12490 161 ≤ (796974049 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (38310597 / 100000000000000000)
  w0 : (tableEnvelope C).w0 12490 161 ≤ (963617677 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12490 161 ≤ (1371191079 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12490 161 ≤ (500999121 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (250496727 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (250496727 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1604462647 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5849812871 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3689293 / 1000000000) : ℝ) ≤ √(17 / (100 * 12490) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12490) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1119144153 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (8011148849 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12490) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12490) ≤ (28306917 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12490) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12490 * (161 : ℝ) ^ 2 + 26 / (10 * 12490) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12490) : ℝ)) (tA 12490 * 161 ^ 2 + 26 / (10 * 12490)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3689293 / 1000000000))) * ((250496727 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3689293 / 1000000000)) ^ 3) * ((1604462647 / 1000000000000000000000000))) + ((5849812871 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3689293 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12490) : ℝ)) d.D d.V d.P (√(tA 12490) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3689293 / 1000000000)) ^ 2 * (((1119144153 / 500000000000000)) * ((8011148849 / 200000000000000000)))) + ((5849812871 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12490) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3689293 / 1000000000)) * ((250496727 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12490) : ℝ)) (tA 12490 * 161 ^ 2 + 26 / (10 * 12490)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((250496727 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3689293 / 1000000000)) ^ 2) * ((1604462647 / 1000000000000000000000000)) + ((5849812871 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12490) : ℝ)) (√(26 / (10 * 12490) : ℝ)) d.D d.V d.P (√(tA 12490) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3689293 / 1000000000)) * (((1119144153 / 500000000000000)) * ((8011148849 / 200000000000000000))) + ((5849812871 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12490) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((250496727 / 50000000000000000000) : ℝ) + ((5849812871 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12490

namespace BstLean.Part266.Row12490
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12490 161 ∧
    0 ≤ (tableEnvelope C).f1 12490 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12490 161 ∧
    0 ≤ (tableEnvelope C).w1 12490 161 ∧ 0 ≤ (tableEnvelope C).w2 12490 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12490 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12490 161 ∧ 0 ≤ d.f1 12490 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12490 161 ∧ 0 ≤ d.w1 12490 161 ∧ 0 ≤ d.w2 12490 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12490 ≤ 2 * (228 / 100 : ℝ) / 12490 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12490 ≤ 2 * (370 / 100 : ℝ) / 12490 := by
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
    (completeRAData (tableEnvelope C) 12490 161).locationBound 12490 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12490 161).energyBound 12490 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12490 161) (d.f1 12490 161) d.f2 ≤
      32 * (((597222453 / 125000000000000000) : ℝ) + (796974049 / 500000000000000000) + (38310597 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12490 161) (d.w1 12490 161)
      (d.w2 12490 161) ≤
      32 * (((963617677 / 50000000000000000000) : ℝ) + (1371191079 / 100000000000000000000) + (500999121 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12490 161) (d.f1 12490 161) d.f2 ≤
      ((597222453 / 125000000000000000) : ℝ) ^ 2 + 2 * ((597222453 / 125000000000000000)) * ((796974049 / 500000000000000000)) * (126 / 100) +
      2 * (((796974049 / 500000000000000000)) ^ 2 + 2 * ((597222453 / 125000000000000000)) * ((38310597 / 100000000000000000))) +
      6 * ((796974049 / 500000000000000000)) * ((38310597 / 100000000000000000)) * (126 / 100) + 8 * ((38310597 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12490 161) (d.f1 12490 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12490 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12490 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12490 161) (d.f1 12490 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12490 161) (d.w1 12490 161) (d.w2 12490 161)
  have hwexpr0 : 0 ≤ d.w0 12490 161 + d.w1 12490 161 * √(π / 2) +
      2 * d.w2 12490 161 + energyR16 12490 *
      radiusPolynomialRoot16 (d.w0 12490 161) (d.w1 12490 161) (d.w2 12490 161) := by
    positivity
  constructor
  · change (12490 : ℝ) ^ 8 * (mA 12490 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12490 161) (d.f1 12490 161) d.f2 + locationR16 12490 *
        radiusPolynomialRoot16 (d.f0 12490 161) (d.f1 12490 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12490 : ℝ) ^ 8 * (mA 12490 : ℝ) ^ 8 *
        ((((597222453 / 125000000000000000) : ℝ) ^ 2 + 2 * ((597222453 / 125000000000000000)) * ((796974049 / 500000000000000000)) * (126 / 100) +
          2 * (((796974049 / 500000000000000000)) ^ 2 + 2 * ((597222453 / 125000000000000000)) * ((38310597 / 100000000000000000))) +
          6 * ((796974049 / 500000000000000000)) * ((38310597 / 100000000000000000)) * (126 / 100) + 8 * ((38310597 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12490) *
          (32 * (((597222453 / 125000000000000000) : ℝ) + (796974049 / 500000000000000000) + (38310597 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12490 : ℝ) ^ 16 *
      (d.w0 12490 161 + d.w1 12490 161 * √(π / 2) + 2 * d.w2 12490 161 +
        energyR16 12490 * radiusPolynomialRoot16 (d.w0 12490 161) (d.w1 12490 161)
          (d.w2 12490 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12490 : ℝ) ^ 16 *
        (((963617677 / 50000000000000000000) : ℝ) + ((1371191079 / 100000000000000000000)) * (126 / 100) + 2 * ((500999121 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12490) *
          (32 * (((963617677 / 50000000000000000000) : ℝ) + (1371191079 / 100000000000000000000) + (500999121 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12490

/-! A coarse bound on the actual paper statistics constant at dimension 12491. -/
namespace BstLean.Part266.Row12491
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12489 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12489 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12489 128 ≤ (12743 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12743 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12491) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12491 : ℕ))
    (by norm_num : (12491 : ℕ) ≤ 16384)
  have ht : paperTail256 12491 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12491 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12491 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12491 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12491 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12491 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12489 128 * √(2 / (12491 : ℝ)) *
      (√(12491 : ℝ) + paperT0 12491 + paperTail256 12491) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12491 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12491 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12491 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12489 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12489 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12491 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12491

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12491
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12491 (61 / 100) 161 (17 / (100 * 12491)) (26 / (10 * 12491)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12491 (61 / 100) 161 (17 / (100 * 12491)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (125218283 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (160394889 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5846030547 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12491 / 12491 * (61 / 100)) ^ 4 * inverseRadius8 (12491 - 1) /
            envelopeGap 12491 (61 / 100) 161 (17 / (100 * 12491)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12491

namespace BstLean.Part266.Row12491
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12491 161 ≤ (4776820829 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12491 161 ≤ (199203561 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (191514611 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12491 161 ≤ (192677197 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12491 161 ≤ (1370861511 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12491 161 ≤ (100175759 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (125218283 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (125218283 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (160394889 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5846030547 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1844573 / 500000000) : ℝ) ≤ √(17 / (100 * 12491) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12491) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2238019509 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40049330707 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12491) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12491) ≤ (113218603 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12491) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12491 * (161 : ℝ) ^ 2 + 26 / (10 * 12491) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12491) : ℝ)) (tA 12491 * 161 ^ 2 + 26 / (10 * 12491)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1844573 / 500000000))) * ((125218283 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1844573 / 500000000)) ^ 3) * ((160394889 / 100000000000000000000000))) + ((5846030547 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1844573 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12491) : ℝ)) d.D d.V d.P (√(tA 12491) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1844573 / 500000000)) ^ 2 * (((2238019509 / 1000000000000000)) * ((40049330707 / 1000000000000000000)))) + ((5846030547 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12491) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1844573 / 500000000)) * ((125218283 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12491) : ℝ)) (tA 12491 * 161 ^ 2 + 26 / (10 * 12491)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((125218283 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1844573 / 500000000)) ^ 2) * ((160394889 / 100000000000000000000000)) + ((5846030547 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12491) : ℝ)) (√(26 / (10 * 12491) : ℝ)) d.D d.V d.P (√(tA 12491) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1844573 / 500000000)) * (((2238019509 / 1000000000000000)) * ((40049330707 / 1000000000000000000))) + ((5846030547 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12491) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((125218283 / 25000000000000000000) : ℝ) + ((5846030547 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12491

namespace BstLean.Part266.Row12491
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12491 161 ∧
    0 ≤ (tableEnvelope C).f1 12491 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12491 161 ∧
    0 ≤ (tableEnvelope C).w1 12491 161 ∧ 0 ≤ (tableEnvelope C).w2 12491 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12491 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12491 161 ∧ 0 ≤ d.f1 12491 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12491 161 ∧ 0 ≤ d.w1 12491 161 ∧ 0 ≤ d.w2 12491 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12491 ≤ 2 * (228 / 100 : ℝ) / 12491 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12491 ≤ 2 * (370 / 100 : ℝ) / 12491 := by
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
    (completeRAData (tableEnvelope C) 12491 161).locationBound 12491 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12491 161).energyBound 12491 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12491 161) (d.f1 12491 161) d.f2 ≤
      32 * (((4776820829 / 1000000000000000000) : ℝ) + (199203561 / 125000000000000000) + (191514611 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12491 161) (d.w1 12491 161)
      (d.w2 12491 161) ≤
      32 * (((192677197 / 10000000000000000000) : ℝ) + (1370861511 / 100000000000000000000) + (100175759 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12491 161) (d.f1 12491 161) d.f2 ≤
      ((4776820829 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4776820829 / 1000000000000000000)) * ((199203561 / 125000000000000000)) * (126 / 100) +
      2 * (((199203561 / 125000000000000000)) ^ 2 + 2 * ((4776820829 / 1000000000000000000)) * ((191514611 / 500000000000000000))) +
      6 * ((199203561 / 125000000000000000)) * ((191514611 / 500000000000000000)) * (126 / 100) + 8 * ((191514611 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12491 161) (d.f1 12491 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12491 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12491 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12491 161) (d.f1 12491 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12491 161) (d.w1 12491 161) (d.w2 12491 161)
  have hwexpr0 : 0 ≤ d.w0 12491 161 + d.w1 12491 161 * √(π / 2) +
      2 * d.w2 12491 161 + energyR16 12491 *
      radiusPolynomialRoot16 (d.w0 12491 161) (d.w1 12491 161) (d.w2 12491 161) := by
    positivity
  constructor
  · change (12491 : ℝ) ^ 8 * (mA 12491 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12491 161) (d.f1 12491 161) d.f2 + locationR16 12491 *
        radiusPolynomialRoot16 (d.f0 12491 161) (d.f1 12491 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12491 : ℝ) ^ 8 * (mA 12491 : ℝ) ^ 8 *
        ((((4776820829 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4776820829 / 1000000000000000000)) * ((199203561 / 125000000000000000)) * (126 / 100) +
          2 * (((199203561 / 125000000000000000)) ^ 2 + 2 * ((4776820829 / 1000000000000000000)) * ((191514611 / 500000000000000000))) +
          6 * ((199203561 / 125000000000000000)) * ((191514611 / 500000000000000000)) * (126 / 100) + 8 * ((191514611 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12491) *
          (32 * (((4776820829 / 1000000000000000000) : ℝ) + (199203561 / 125000000000000000) + (191514611 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12491 : ℝ) ^ 16 *
      (d.w0 12491 161 + d.w1 12491 161 * √(π / 2) + 2 * d.w2 12491 161 +
        energyR16 12491 * radiusPolynomialRoot16 (d.w0 12491 161) (d.w1 12491 161)
          (d.w2 12491 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12491 : ℝ) ^ 16 *
        (((192677197 / 10000000000000000000) : ℝ) + ((1370861511 / 100000000000000000000)) * (126 / 100) + 2 * ((100175759 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12491) *
          (32 * (((192677197 / 10000000000000000000) : ℝ) + (1370861511 / 100000000000000000000) + (100175759 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12491

/-! A coarse bound on the actual paper statistics constant at dimension 12492. -/
namespace BstLean.Part266.Row12492
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12490 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12490 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12490 128 ≤ (12744 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12744 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12492) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12492 : ℕ))
    (by norm_num : (12492 : ℕ) ≤ 16384)
  have ht : paperTail256 12492 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12492 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12492 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12492 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12492 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12492 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12490 128 * √(2 / (12492 : ℝ)) *
      (√(12492 : ℝ) + paperT0 12492 + paperTail256 12492) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12492 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12492 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12492 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12490 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12490 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12492 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12492

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12492
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12492 (61 / 100) 161 (17 / (100 * 12492)) (26 / (10 * 12492)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12492 (61 / 100) 161 (17 / (100 * 12492)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (500752849 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (801717669 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (182570343 / 31250000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12492 / 12492 * (61 / 100)) ^ 4 * inverseRadius8 (12492 - 1) /
            envelopeGap 12492 (61 / 100) 161 (17 / (100 * 12492)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12492

namespace BstLean.Part266.Row12492
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12492 161 ≤ (2387933053 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12492 161 ≤ (199163731 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (191476301 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12492 161 ≤ (24078869 / 1250000000000000000)
  w1 : (tableEnvelope C).w1 12492 161 ≤ (1370532427 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12492 161 ≤ (500758509 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (500752849 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (500752849 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (801717669 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (182570343 / 31250000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1844499 / 500000000) : ℝ) ≤ √(17 / (100 * 12492) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12492) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1118875383 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (400429187 / 10000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12492) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12492) ≤ (5660477 / 50000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12492) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12492 * (161 : ℝ) ^ 2 + 26 / (10 * 12492) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12492) : ℝ)) (tA 12492 * 161 ^ 2 + 26 / (10 * 12492)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1844499 / 500000000))) * ((500752849 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1844499 / 500000000)) ^ 3) * ((801717669 / 500000000000000000000000))) + ((182570343 / 31250000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1844499 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12492) : ℝ)) d.D d.V d.P (√(tA 12492) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1844499 / 500000000)) ^ 2 * (((1118875383 / 500000000000000)) * ((400429187 / 10000000000000000)))) + ((182570343 / 31250000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12492) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1844499 / 500000000)) * ((500752849 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12492) : ℝ)) (tA 12492 * 161 ^ 2 + 26 / (10 * 12492)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((500752849 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1844499 / 500000000)) ^ 2) * ((801717669 / 500000000000000000000000)) + ((182570343 / 31250000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12492) : ℝ)) (√(26 / (10 * 12492) : ℝ)) d.D d.V d.P (√(tA 12492) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1844499 / 500000000)) * (((1118875383 / 500000000000000)) * ((400429187 / 10000000000000000))) + ((182570343 / 31250000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12492) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((500752849 / 100000000000000000000) : ℝ) + ((182570343 / 31250000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12492

namespace BstLean.Part266.Row12492
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12492 161 ∧
    0 ≤ (tableEnvelope C).f1 12492 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12492 161 ∧
    0 ≤ (tableEnvelope C).w1 12492 161 ∧ 0 ≤ (tableEnvelope C).w2 12492 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12492 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12492 161 ∧ 0 ≤ d.f1 12492 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12492 161 ∧ 0 ≤ d.w1 12492 161 ∧ 0 ≤ d.w2 12492 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12492 ≤ 2 * (228 / 100 : ℝ) / 12492 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12492 ≤ 2 * (370 / 100 : ℝ) / 12492 := by
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
    (completeRAData (tableEnvelope C) 12492 161).locationBound 12492 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12492 161).energyBound 12492 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12492 161) (d.f1 12492 161) d.f2 ≤
      32 * (((2387933053 / 500000000000000000) : ℝ) + (199163731 / 125000000000000000) + (191476301 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12492 161) (d.w1 12492 161)
      (d.w2 12492 161) ≤
      32 * (((24078869 / 1250000000000000000) : ℝ) + (1370532427 / 100000000000000000000) + (500758509 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12492 161) (d.f1 12492 161) d.f2 ≤
      ((2387933053 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2387933053 / 500000000000000000)) * ((199163731 / 125000000000000000)) * (126 / 100) +
      2 * (((199163731 / 125000000000000000)) ^ 2 + 2 * ((2387933053 / 500000000000000000)) * ((191476301 / 500000000000000000))) +
      6 * ((199163731 / 125000000000000000)) * ((191476301 / 500000000000000000)) * (126 / 100) + 8 * ((191476301 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12492 161) (d.f1 12492 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12492 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12492 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12492 161) (d.f1 12492 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12492 161) (d.w1 12492 161) (d.w2 12492 161)
  have hwexpr0 : 0 ≤ d.w0 12492 161 + d.w1 12492 161 * √(π / 2) +
      2 * d.w2 12492 161 + energyR16 12492 *
      radiusPolynomialRoot16 (d.w0 12492 161) (d.w1 12492 161) (d.w2 12492 161) := by
    positivity
  constructor
  · change (12492 : ℝ) ^ 8 * (mA 12492 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12492 161) (d.f1 12492 161) d.f2 + locationR16 12492 *
        radiusPolynomialRoot16 (d.f0 12492 161) (d.f1 12492 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12492 : ℝ) ^ 8 * (mA 12492 : ℝ) ^ 8 *
        ((((2387933053 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2387933053 / 500000000000000000)) * ((199163731 / 125000000000000000)) * (126 / 100) +
          2 * (((199163731 / 125000000000000000)) ^ 2 + 2 * ((2387933053 / 500000000000000000)) * ((191476301 / 500000000000000000))) +
          6 * ((199163731 / 125000000000000000)) * ((191476301 / 500000000000000000)) * (126 / 100) + 8 * ((191476301 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12492) *
          (32 * (((2387933053 / 500000000000000000) : ℝ) + (199163731 / 125000000000000000) + (191476301 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12492 : ℝ) ^ 16 *
      (d.w0 12492 161 + d.w1 12492 161 * √(π / 2) + 2 * d.w2 12492 161 +
        energyR16 12492 * radiusPolynomialRoot16 (d.w0 12492 161) (d.w1 12492 161)
          (d.w2 12492 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12492 : ℝ) ^ 16 *
        (((24078869 / 1250000000000000000) : ℝ) + ((1370532427 / 100000000000000000000)) * (126 / 100) + 2 * ((500758509 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12492) *
          (32 * (((24078869 / 1250000000000000000) : ℝ) + (1370532427 / 100000000000000000000) + (500758509 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12492

/-! A coarse bound on the actual paper statistics constant at dimension 12493. -/
namespace BstLean.Part266.Row12493
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12491 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12491 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12491 128 ≤ (12745 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12745 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12493) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12493 : ℕ))
    (by norm_num : (12493 : ℕ) ≤ 16384)
  have ht : paperTail256 12493 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12493 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12493 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12493 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12493 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12493 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12491 128 * √(2 / (12493 : ℝ)) *
      (√(12493 : ℝ) + paperT0 12493 + paperTail256 12493) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12493 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12493 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12493 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12491 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12491 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12493 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12493

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12493
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12493 (61 / 100) 161 (17 / (100 * 12493)) (26 / (10 * 12493)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12493 (61 / 100) 161 (17 / (100 * 12493)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (125158151 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1602921993 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2919237079 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12493 / 12493 * (61 / 100)) ^ 4 * inverseRadius8 (12493 - 1) /
            envelopeGap 12493 (61 / 100) 161 (17 / (100 * 12493)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12493

namespace BstLean.Part266.Row12493
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12493 161 ≤ (4774911719 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12493 161 ≤ (99561957 / 62500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (76575201 / 200000000000000000)
  w0 : (tableEnvelope C).w0 12493 161 ≤ (1925847233 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12493 161 ≤ (274040691 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 12493 161 ≤ (25031913 / 5000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (125158151 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (125158151 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1602921993 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2919237079 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((73777 / 20000000) : ℝ) ≤ √(17 / (100 * 12493) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12493) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (559370519 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (10009127063 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12493) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12493) ≤ (56600239 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12493) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12493 * (161 : ℝ) ^ 2 + 26 / (10 * 12493) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12493) : ℝ)) (tA 12493 * 161 ^ 2 + 26 / (10 * 12493)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((73777 / 20000000))) * ((125158151 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((73777 / 20000000)) ^ 3) * ((1602921993 / 1000000000000000000000000))) + ((2919237079 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((73777 / 20000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12493) : ℝ)) d.D d.V d.P (√(tA 12493) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((73777 / 20000000)) ^ 2 * (((559370519 / 250000000000000)) * ((10009127063 / 250000000000000000)))) + ((2919237079 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12493) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((73777 / 20000000)) * ((125158151 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12493) : ℝ)) (tA 12493 * 161 ^ 2 + 26 / (10 * 12493)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((125158151 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((73777 / 20000000)) ^ 2) * ((1602921993 / 1000000000000000000000000)) + ((2919237079 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12493) : ℝ)) (√(26 / (10 * 12493) : ℝ)) d.D d.V d.P (√(tA 12493) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((73777 / 20000000)) * (((559370519 / 250000000000000)) * ((10009127063 / 250000000000000000))) + ((2919237079 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12493) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((125158151 / 25000000000000000000) : ℝ) + ((2919237079 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12493

namespace BstLean.Part266.Row12493
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12493 161 ∧
    0 ≤ (tableEnvelope C).f1 12493 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12493 161 ∧
    0 ≤ (tableEnvelope C).w1 12493 161 ∧ 0 ≤ (tableEnvelope C).w2 12493 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12493 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12493 161 ∧ 0 ≤ d.f1 12493 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12493 161 ∧ 0 ≤ d.w1 12493 161 ∧ 0 ≤ d.w2 12493 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12493 ≤ 2 * (228 / 100 : ℝ) / 12493 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12493 ≤ 2 * (370 / 100 : ℝ) / 12493 := by
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
    (completeRAData (tableEnvelope C) 12493 161).locationBound 12493 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12493 161).energyBound 12493 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12493 161) (d.f1 12493 161) d.f2 ≤
      32 * (((4774911719 / 1000000000000000000) : ℝ) + (99561957 / 62500000000000000) + (76575201 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12493 161) (d.w1 12493 161)
      (d.w2 12493 161) ≤
      32 * (((1925847233 / 100000000000000000000) : ℝ) + (274040691 / 20000000000000000000) + (25031913 / 5000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12493 161) (d.f1 12493 161) d.f2 ≤
      ((4774911719 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4774911719 / 1000000000000000000)) * ((99561957 / 62500000000000000)) * (126 / 100) +
      2 * (((99561957 / 62500000000000000)) ^ 2 + 2 * ((4774911719 / 1000000000000000000)) * ((76575201 / 200000000000000000))) +
      6 * ((99561957 / 62500000000000000)) * ((76575201 / 200000000000000000)) * (126 / 100) + 8 * ((76575201 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12493 161) (d.f1 12493 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12493 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12493 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12493 161) (d.f1 12493 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12493 161) (d.w1 12493 161) (d.w2 12493 161)
  have hwexpr0 : 0 ≤ d.w0 12493 161 + d.w1 12493 161 * √(π / 2) +
      2 * d.w2 12493 161 + energyR16 12493 *
      radiusPolynomialRoot16 (d.w0 12493 161) (d.w1 12493 161) (d.w2 12493 161) := by
    positivity
  constructor
  · change (12493 : ℝ) ^ 8 * (mA 12493 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12493 161) (d.f1 12493 161) d.f2 + locationR16 12493 *
        radiusPolynomialRoot16 (d.f0 12493 161) (d.f1 12493 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12493 : ℝ) ^ 8 * (mA 12493 : ℝ) ^ 8 *
        ((((4774911719 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4774911719 / 1000000000000000000)) * ((99561957 / 62500000000000000)) * (126 / 100) +
          2 * (((99561957 / 62500000000000000)) ^ 2 + 2 * ((4774911719 / 1000000000000000000)) * ((76575201 / 200000000000000000))) +
          6 * ((99561957 / 62500000000000000)) * ((76575201 / 200000000000000000)) * (126 / 100) + 8 * ((76575201 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12493) *
          (32 * (((4774911719 / 1000000000000000000) : ℝ) + (99561957 / 62500000000000000) + (76575201 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12493 : ℝ) ^ 16 *
      (d.w0 12493 161 + d.w1 12493 161 * √(π / 2) + 2 * d.w2 12493 161 +
        energyR16 12493 * radiusPolynomialRoot16 (d.w0 12493 161) (d.w1 12493 161)
          (d.w2 12493 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12493 : ℝ) ^ 16 *
        (((1925847233 / 100000000000000000000) : ℝ) + ((274040691 / 20000000000000000000)) * (126 / 100) + 2 * ((25031913 / 5000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12493) *
          (32 * (((1925847233 / 100000000000000000000) : ℝ) + (274040691 / 20000000000000000000) + (25031913 / 5000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12493

/-! A coarse bound on the actual paper statistics constant at dimension 12494. -/
namespace BstLean.Part266.Row12494
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12492 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12492 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12492 128 ≤ (12746 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12746 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12494) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12494 : ℕ))
    (by norm_num : (12494 : ℕ) ≤ 16384)
  have ht : paperTail256 12494 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12494 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12494 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12494 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12494 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12494 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12492 128 * √(2 / (12494 : ℝ)) *
      (√(12494 : ℝ) + paperT0 12494 + paperTail256 12494) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12494 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12494 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12494 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12492 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12492 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12494 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12494

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12494
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12494 (61 / 100) 161 (17 / (100 * 12494)) (26 / (10 * 12494)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12494 (61 / 100) 161 (17 / (100 * 12494)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (250256199 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (400602213 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5834700089 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12494 / 12494 * (61 / 100)) ^ 4 * inverseRadius8 (12494 - 1) /
            envelopeGap 12494 (61 / 100) 161 (17 / (100 * 12494)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12494

namespace BstLean.Part266.Row12494
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12494 161 ≤ (4773953927 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12494 161 ≤ (1592672017 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (11962479 / 31250000000000000)
  w0 : (tableEnvelope C).w0 12494 161 ≤ (962692167 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12494 161 ≤ (85617139 / 6250000000000000000)
  w2 : (tableEnvelope C).w2 12494 161 ≤ (500518051 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (250256199 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (250256199 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (400602213 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5834700089 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3688703 / 1000000000) : ℝ) ≤ √(17 / (100 * 12494) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12494) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2237213441 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (20015049663 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12494) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12494) ≤ (113191417 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12494) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12494 * (161 : ℝ) ^ 2 + 26 / (10 * 12494) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12494) : ℝ)) (tA 12494 * 161 ^ 2 + 26 / (10 * 12494)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3688703 / 1000000000))) * ((250256199 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3688703 / 1000000000)) ^ 3) * ((400602213 / 250000000000000000000000))) + ((5834700089 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3688703 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12494) : ℝ)) d.D d.V d.P (√(tA 12494) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3688703 / 1000000000)) ^ 2 * (((2237213441 / 1000000000000000)) * ((20015049663 / 500000000000000000)))) + ((5834700089 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12494) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3688703 / 1000000000)) * ((250256199 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12494) : ℝ)) (tA 12494 * 161 ^ 2 + 26 / (10 * 12494)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((250256199 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3688703 / 1000000000)) ^ 2) * ((400602213 / 250000000000000000000000)) + ((5834700089 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12494) : ℝ)) (√(26 / (10 * 12494) : ℝ)) d.D d.V d.P (√(tA 12494) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3688703 / 1000000000)) * (((2237213441 / 1000000000000000)) * ((20015049663 / 500000000000000000))) + ((5834700089 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12494) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((250256199 / 50000000000000000000) : ℝ) + ((5834700089 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12494

namespace BstLean.Part266.Row12494
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12494 161 ∧
    0 ≤ (tableEnvelope C).f1 12494 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12494 161 ∧
    0 ≤ (tableEnvelope C).w1 12494 161 ∧ 0 ≤ (tableEnvelope C).w2 12494 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12494 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12494 161 ∧ 0 ≤ d.f1 12494 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12494 161 ∧ 0 ≤ d.w1 12494 161 ∧ 0 ≤ d.w2 12494 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12494 ≤ 2 * (228 / 100 : ℝ) / 12494 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12494 ≤ 2 * (370 / 100 : ℝ) / 12494 := by
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
    (completeRAData (tableEnvelope C) 12494 161).locationBound 12494 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12494 161).energyBound 12494 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12494 161) (d.f1 12494 161) d.f2 ≤
      32 * (((4773953927 / 1000000000000000000) : ℝ) + (1592672017 / 1000000000000000000) + (11962479 / 31250000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12494 161) (d.w1 12494 161)
      (d.w2 12494 161) ≤
      32 * (((962692167 / 50000000000000000000) : ℝ) + (85617139 / 6250000000000000000) + (500518051 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12494 161) (d.f1 12494 161) d.f2 ≤
      ((4773953927 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4773953927 / 1000000000000000000)) * ((1592672017 / 1000000000000000000)) * (126 / 100) +
      2 * (((1592672017 / 1000000000000000000)) ^ 2 + 2 * ((4773953927 / 1000000000000000000)) * ((11962479 / 31250000000000000))) +
      6 * ((1592672017 / 1000000000000000000)) * ((11962479 / 31250000000000000)) * (126 / 100) + 8 * ((11962479 / 31250000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12494 161) (d.f1 12494 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12494 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12494 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12494 161) (d.f1 12494 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12494 161) (d.w1 12494 161) (d.w2 12494 161)
  have hwexpr0 : 0 ≤ d.w0 12494 161 + d.w1 12494 161 * √(π / 2) +
      2 * d.w2 12494 161 + energyR16 12494 *
      radiusPolynomialRoot16 (d.w0 12494 161) (d.w1 12494 161) (d.w2 12494 161) := by
    positivity
  constructor
  · change (12494 : ℝ) ^ 8 * (mA 12494 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12494 161) (d.f1 12494 161) d.f2 + locationR16 12494 *
        radiusPolynomialRoot16 (d.f0 12494 161) (d.f1 12494 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12494 : ℝ) ^ 8 * (mA 12494 : ℝ) ^ 8 *
        ((((4773953927 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4773953927 / 1000000000000000000)) * ((1592672017 / 1000000000000000000)) * (126 / 100) +
          2 * (((1592672017 / 1000000000000000000)) ^ 2 + 2 * ((4773953927 / 1000000000000000000)) * ((11962479 / 31250000000000000))) +
          6 * ((1592672017 / 1000000000000000000)) * ((11962479 / 31250000000000000)) * (126 / 100) + 8 * ((11962479 / 31250000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12494) *
          (32 * (((4773953927 / 1000000000000000000) : ℝ) + (1592672017 / 1000000000000000000) + (11962479 / 31250000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12494 : ℝ) ^ 16 *
      (d.w0 12494 161 + d.w1 12494 161 * √(π / 2) + 2 * d.w2 12494 161 +
        energyR16 12494 * radiusPolynomialRoot16 (d.w0 12494 161) (d.w1 12494 161)
          (d.w2 12494 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12494 : ℝ) ^ 16 *
        (((962692167 / 50000000000000000000) : ℝ) + ((85617139 / 6250000000000000000)) * (126 / 100) + 2 * ((500518051 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12494) *
          (32 * (((962692167 / 50000000000000000000) : ℝ) + (85617139 / 6250000000000000000) + (500518051 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12494

/-! A coarse bound on the actual paper statistics constant at dimension 12495. -/
namespace BstLean.Part266.Row12495
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12493 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12493 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12493 128 ≤ (12747 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12747 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12495) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12495 : ℕ))
    (by norm_num : (12495 : ℕ) ≤ 16384)
  have ht : paperTail256 12495 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12495 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12495 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12495 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12495 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12495 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12493 128 * √(2 / (12495 : ℝ)) *
      (√(12495 : ℝ) + paperT0 12495 + paperTail256 12495) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12495 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12495 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12495 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12493 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12493 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12495 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12495

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12495
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12495 (61 / 100) 161 (17 / (100 * 12495)) (26 / (10 * 12495)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12495 (61 / 100) 161 (17 / (100 * 12495)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (50039223 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1601895917 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5830928767 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12495 / 12495 * (61 / 100)) ^ 4 * inverseRadius8 (12495 - 1) /
            envelopeGap 12495 (61 / 100) 161 (17 / (100 * 12495)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12495

namespace BstLean.Part266.Row12495
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12495 161 ≤ (2386500103 / 500000000000000000)
  f1 : (tableEnvelope C).f1 12495 161 ≤ (159235369 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (382722777 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12495 161 ≤ (192492237 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 12495 161 ≤ (54781819 / 4000000000000000000)
  w2 : (tableEnvelope C).w2 12495 161 ≤ (500397879 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (50039223 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (50039223 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1601895917 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5830928767 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((737711 / 200000000) : ℝ) ≤ √(17 / (100 * 12495) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12495) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2236944859 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40023691947 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12495) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12495) ≤ (56591179 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12495) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12495 * (161 : ℝ) ^ 2 + 26 / (10 * 12495) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12495) : ℝ)) (tA 12495 * 161 ^ 2 + 26 / (10 * 12495)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((737711 / 200000000))) * ((50039223 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((737711 / 200000000)) ^ 3) * ((1601895917 / 1000000000000000000000000))) + ((5830928767 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((737711 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12495) : ℝ)) d.D d.V d.P (√(tA 12495) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((737711 / 200000000)) ^ 2 * (((2236944859 / 1000000000000000)) * ((40023691947 / 1000000000000000000)))) + ((5830928767 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12495) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((737711 / 200000000)) * ((50039223 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12495) : ℝ)) (tA 12495 * 161 ^ 2 + 26 / (10 * 12495)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((50039223 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((737711 / 200000000)) ^ 2) * ((1601895917 / 1000000000000000000000000)) + ((5830928767 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12495) : ℝ)) (√(26 / (10 * 12495) : ℝ)) d.D d.V d.P (√(tA 12495) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((737711 / 200000000)) * (((2236944859 / 1000000000000000)) * ((40023691947 / 1000000000000000000))) + ((5830928767 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12495) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((50039223 / 10000000000000000000) : ℝ) + ((5830928767 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12495

namespace BstLean.Part266.Row12495
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12495 161 ∧
    0 ≤ (tableEnvelope C).f1 12495 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12495 161 ∧
    0 ≤ (tableEnvelope C).w1 12495 161 ∧ 0 ≤ (tableEnvelope C).w2 12495 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12495 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12495 161 ∧ 0 ≤ d.f1 12495 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12495 161 ∧ 0 ≤ d.w1 12495 161 ∧ 0 ≤ d.w2 12495 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12495 ≤ 2 * (228 / 100 : ℝ) / 12495 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12495 ≤ 2 * (370 / 100 : ℝ) / 12495 := by
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
    (completeRAData (tableEnvelope C) 12495 161).locationBound 12495 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12495 161).energyBound 12495 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12495 161) (d.f1 12495 161) d.f2 ≤
      32 * (((2386500103 / 500000000000000000) : ℝ) + (159235369 / 100000000000000000) + (382722777 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12495 161) (d.w1 12495 161)
      (d.w2 12495 161) ≤
      32 * (((192492237 / 10000000000000000000) : ℝ) + (54781819 / 4000000000000000000) + (500397879 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12495 161) (d.f1 12495 161) d.f2 ≤
      ((2386500103 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2386500103 / 500000000000000000)) * ((159235369 / 100000000000000000)) * (126 / 100) +
      2 * (((159235369 / 100000000000000000)) ^ 2 + 2 * ((2386500103 / 500000000000000000)) * ((382722777 / 1000000000000000000))) +
      6 * ((159235369 / 100000000000000000)) * ((382722777 / 1000000000000000000)) * (126 / 100) + 8 * ((382722777 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12495 161) (d.f1 12495 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12495 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12495 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12495 161) (d.f1 12495 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12495 161) (d.w1 12495 161) (d.w2 12495 161)
  have hwexpr0 : 0 ≤ d.w0 12495 161 + d.w1 12495 161 * √(π / 2) +
      2 * d.w2 12495 161 + energyR16 12495 *
      radiusPolynomialRoot16 (d.w0 12495 161) (d.w1 12495 161) (d.w2 12495 161) := by
    positivity
  constructor
  · change (12495 : ℝ) ^ 8 * (mA 12495 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12495 161) (d.f1 12495 161) d.f2 + locationR16 12495 *
        radiusPolynomialRoot16 (d.f0 12495 161) (d.f1 12495 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12495 : ℝ) ^ 8 * (mA 12495 : ℝ) ^ 8 *
        ((((2386500103 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2386500103 / 500000000000000000)) * ((159235369 / 100000000000000000)) * (126 / 100) +
          2 * (((159235369 / 100000000000000000)) ^ 2 + 2 * ((2386500103 / 500000000000000000)) * ((382722777 / 1000000000000000000))) +
          6 * ((159235369 / 100000000000000000)) * ((382722777 / 1000000000000000000)) * (126 / 100) + 8 * ((382722777 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12495) *
          (32 * (((2386500103 / 500000000000000000) : ℝ) + (159235369 / 100000000000000000) + (382722777 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12495 : ℝ) ^ 16 *
      (d.w0 12495 161 + d.w1 12495 161 * √(π / 2) + 2 * d.w2 12495 161 +
        energyR16 12495 * radiusPolynomialRoot16 (d.w0 12495 161) (d.w1 12495 161)
          (d.w2 12495 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12495 : ℝ) ^ 16 *
        (((192492237 / 10000000000000000000) : ℝ) + ((54781819 / 4000000000000000000)) * (126 / 100) + 2 * ((500397879 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12495) *
          (32 * (((192492237 / 10000000000000000000) : ℝ) + (54781819 / 4000000000000000000) + (500397879 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12495

/-! A coarse bound on the actual paper statistics constant at dimension 12496. -/
namespace BstLean.Part266.Row12496
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12494 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12494 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12494 128 ≤ (12748 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12748 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12496) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12496 : ℕ))
    (by norm_num : (12496 : ℕ) ≤ 16384)
  have ht : paperTail256 12496 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12496 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12496 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12496 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12496 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12496 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12494 128 * √(2 / (12496 : ℝ)) *
      (√(12496 : ℝ) + paperT0 12496 + paperTail256 12496) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12496 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12496 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12496 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12494 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12494 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12496 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12496

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12496
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12496 (61 / 100) 161 (17 / (100 * 12496)) (26 / (10 * 12496)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12496 (61 / 100) 161 (17 / (100 * 12496)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (5002721 / 1000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (400345797 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (582716019 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12496 / 12496 * (61 / 100)) ^ 4 * inverseRadius8 (12496 - 1) /
            envelopeGap 12496 (61 / 100) 161 (17 / (100 * 12496)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12496

namespace BstLean.Part266.Row12496
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12496 161 ≤ (4772046821 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12496 161 ≤ (1592035467 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (306117 / 800000000000000)
  w0 : (tableEnvelope C).w0 12496 161 ≤ (1924460567 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12496 161 ≤ (684608419 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12496 161 ≤ (100055549 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (5002721 / 1000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (5002721 / 1000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (400345797 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (582716019 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3688407 / 1000000000) : ℝ) ≤ √(17 / (100 * 12496) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12496) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2236676329 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (8003457223 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12496) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12496) ≤ (113173301 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12496) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12496 * (161 : ℝ) ^ 2 + 26 / (10 * 12496) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12496) : ℝ)) (tA 12496 * 161 ^ 2 + 26 / (10 * 12496)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3688407 / 1000000000))) * ((5002721 / 1000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3688407 / 1000000000)) ^ 3) * ((400345797 / 250000000000000000000000))) + ((582716019 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3688407 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12496) : ℝ)) d.D d.V d.P (√(tA 12496) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3688407 / 1000000000)) ^ 2 * (((2236676329 / 1000000000000000)) * ((8003457223 / 200000000000000000)))) + ((582716019 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12496) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3688407 / 1000000000)) * ((5002721 / 1000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12496) : ℝ)) (tA 12496 * 161 ^ 2 + 26 / (10 * 12496)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((5002721 / 1000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3688407 / 1000000000)) ^ 2) * ((400345797 / 250000000000000000000000)) + ((582716019 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12496) : ℝ)) (√(26 / (10 * 12496) : ℝ)) d.D d.V d.P (√(tA 12496) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3688407 / 1000000000)) * (((2236676329 / 1000000000000000)) * ((8003457223 / 200000000000000000))) + ((582716019 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12496) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((5002721 / 1000000000000000000) : ℝ) + ((582716019 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12496

namespace BstLean.Part266.Row12496
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12496 161 ∧
    0 ≤ (tableEnvelope C).f1 12496 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12496 161 ∧
    0 ≤ (tableEnvelope C).w1 12496 161 ∧ 0 ≤ (tableEnvelope C).w2 12496 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12496 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12496 161 ∧ 0 ≤ d.f1 12496 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12496 161 ∧ 0 ≤ d.w1 12496 161 ∧ 0 ≤ d.w2 12496 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12496 ≤ 2 * (228 / 100 : ℝ) / 12496 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12496 ≤ 2 * (370 / 100 : ℝ) / 12496 := by
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
    (completeRAData (tableEnvelope C) 12496 161).locationBound 12496 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12496 161).energyBound 12496 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12496 161) (d.f1 12496 161) d.f2 ≤
      32 * (((4772046821 / 1000000000000000000) : ℝ) + (1592035467 / 1000000000000000000) + (306117 / 800000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12496 161) (d.w1 12496 161)
      (d.w2 12496 161) ≤
      32 * (((1924460567 / 100000000000000000000) : ℝ) + (684608419 / 50000000000000000000) + (100055549 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12496 161) (d.f1 12496 161) d.f2 ≤
      ((4772046821 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4772046821 / 1000000000000000000)) * ((1592035467 / 1000000000000000000)) * (126 / 100) +
      2 * (((1592035467 / 1000000000000000000)) ^ 2 + 2 * ((4772046821 / 1000000000000000000)) * ((306117 / 800000000000000))) +
      6 * ((1592035467 / 1000000000000000000)) * ((306117 / 800000000000000)) * (126 / 100) + 8 * ((306117 / 800000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12496 161) (d.f1 12496 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12496 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12496 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12496 161) (d.f1 12496 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12496 161) (d.w1 12496 161) (d.w2 12496 161)
  have hwexpr0 : 0 ≤ d.w0 12496 161 + d.w1 12496 161 * √(π / 2) +
      2 * d.w2 12496 161 + energyR16 12496 *
      radiusPolynomialRoot16 (d.w0 12496 161) (d.w1 12496 161) (d.w2 12496 161) := by
    positivity
  constructor
  · change (12496 : ℝ) ^ 8 * (mA 12496 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12496 161) (d.f1 12496 161) d.f2 + locationR16 12496 *
        radiusPolynomialRoot16 (d.f0 12496 161) (d.f1 12496 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12496 : ℝ) ^ 8 * (mA 12496 : ℝ) ^ 8 *
        ((((4772046821 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4772046821 / 1000000000000000000)) * ((1592035467 / 1000000000000000000)) * (126 / 100) +
          2 * (((1592035467 / 1000000000000000000)) ^ 2 + 2 * ((4772046821 / 1000000000000000000)) * ((306117 / 800000000000000))) +
          6 * ((1592035467 / 1000000000000000000)) * ((306117 / 800000000000000)) * (126 / 100) + 8 * ((306117 / 800000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12496) *
          (32 * (((4772046821 / 1000000000000000000) : ℝ) + (1592035467 / 1000000000000000000) + (306117 / 800000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12496 : ℝ) ^ 16 *
      (d.w0 12496 161 + d.w1 12496 161 * √(π / 2) + 2 * d.w2 12496 161 +
        energyR16 12496 * radiusPolynomialRoot16 (d.w0 12496 161) (d.w1 12496 161)
          (d.w2 12496 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12496 : ℝ) ^ 16 *
        (((1924460567 / 100000000000000000000) : ℝ) + ((684608419 / 50000000000000000000)) * (126 / 100) + 2 * ((100055549 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12496) *
          (32 * (((1924460567 / 100000000000000000000) : ℝ) + (684608419 / 50000000000000000000) + (100055549 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12496

/-! A coarse bound on the actual paper statistics constant at dimension 12497. -/
namespace BstLean.Part266.Row12497
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12495 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12495 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12495 128 ≤ (12749 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12749 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12497) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12497 : ℕ))
    (by norm_num : (12497 : ℕ) ≤ 16384)
  have ht : paperTail256 12497 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12497 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12497 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12497 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12497 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12497 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12495 128 * √(2 / (12497 : ℝ)) *
      (√(12497 : ℝ) + paperT0 12497 + paperTail256 12497) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12497 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12497 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12497 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12495 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12495 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12497 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12497

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12497
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12497 (61 / 100) 161 (17 / (100 * 12497)) (26 / (10 * 12497)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12497 (61 / 100) 161 (17 / (100 * 12497)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (500152009 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1600870663 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1455848589 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12497 / 12497 * (61 / 100)) ^ 4 * inverseRadius8 (12497 - 1) /
            envelopeGap 12497 (61 / 100) 161 (17 / (100 * 12497)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12497

namespace BstLean.Part266.Row12497
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12497 161 ≤ (4771090031 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12497 161 ≤ (795858243 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (191284821 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12497 161 ≤ (1923998153 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 12497 161 ≤ (1368887943 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 12497 161 ≤ (500157651 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (500152009 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (500152009 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1600870663 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1455848589 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((184413 / 50000000) : ℝ) ≤ √(17 / (100 * 12497) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12497) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (447281571 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (2500680113 / 62500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12497) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12497) ≤ (22632849 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12497) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12497 * (161 : ℝ) ^ 2 + 26 / (10 * 12497) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12497) : ℝ)) (tA 12497 * 161 ^ 2 + 26 / (10 * 12497)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((184413 / 50000000))) * ((500152009 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((184413 / 50000000)) ^ 3) * ((1600870663 / 1000000000000000000000000))) + ((1455848589 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((184413 / 50000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12497) : ℝ)) d.D d.V d.P (√(tA 12497) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((184413 / 50000000)) ^ 2 * (((447281571 / 200000000000000)) * ((2500680113 / 62500000000000000)))) + ((1455848589 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12497) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((184413 / 50000000)) * ((500152009 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12497) : ℝ)) (tA 12497 * 161 ^ 2 + 26 / (10 * 12497)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((500152009 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((184413 / 50000000)) ^ 2) * ((1600870663 / 1000000000000000000000000)) + ((1455848589 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12497) : ℝ)) (√(26 / (10 * 12497) : ℝ)) d.D d.V d.P (√(tA 12497) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((184413 / 50000000)) * (((447281571 / 200000000000000)) * ((2500680113 / 62500000000000000))) + ((1455848589 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12497) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((500152009 / 100000000000000000000) : ℝ) + ((1455848589 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12497

namespace BstLean.Part266.Row12497
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12497 161 ∧
    0 ≤ (tableEnvelope C).f1 12497 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12497 161 ∧
    0 ≤ (tableEnvelope C).w1 12497 161 ∧ 0 ≤ (tableEnvelope C).w2 12497 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12497 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12497 161 ∧ 0 ≤ d.f1 12497 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12497 161 ∧ 0 ≤ d.w1 12497 161 ∧ 0 ≤ d.w2 12497 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12497 ≤ 2 * (228 / 100 : ℝ) / 12497 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12497 ≤ 2 * (370 / 100 : ℝ) / 12497 := by
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
    (completeRAData (tableEnvelope C) 12497 161).locationBound 12497 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12497 161).energyBound 12497 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12497 161) (d.f1 12497 161) d.f2 ≤
      32 * (((4771090031 / 1000000000000000000) : ℝ) + (795858243 / 500000000000000000) + (191284821 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12497 161) (d.w1 12497 161)
      (d.w2 12497 161) ≤
      32 * (((1923998153 / 100000000000000000000) : ℝ) + (1368887943 / 100000000000000000000) + (500157651 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12497 161) (d.f1 12497 161) d.f2 ≤
      ((4771090031 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4771090031 / 1000000000000000000)) * ((795858243 / 500000000000000000)) * (126 / 100) +
      2 * (((795858243 / 500000000000000000)) ^ 2 + 2 * ((4771090031 / 1000000000000000000)) * ((191284821 / 500000000000000000))) +
      6 * ((795858243 / 500000000000000000)) * ((191284821 / 500000000000000000)) * (126 / 100) + 8 * ((191284821 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12497 161) (d.f1 12497 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12497 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12497 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12497 161) (d.f1 12497 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12497 161) (d.w1 12497 161) (d.w2 12497 161)
  have hwexpr0 : 0 ≤ d.w0 12497 161 + d.w1 12497 161 * √(π / 2) +
      2 * d.w2 12497 161 + energyR16 12497 *
      radiusPolynomialRoot16 (d.w0 12497 161) (d.w1 12497 161) (d.w2 12497 161) := by
    positivity
  constructor
  · change (12497 : ℝ) ^ 8 * (mA 12497 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12497 161) (d.f1 12497 161) d.f2 + locationR16 12497 *
        radiusPolynomialRoot16 (d.f0 12497 161) (d.f1 12497 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12497 : ℝ) ^ 8 * (mA 12497 : ℝ) ^ 8 *
        ((((4771090031 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4771090031 / 1000000000000000000)) * ((795858243 / 500000000000000000)) * (126 / 100) +
          2 * (((795858243 / 500000000000000000)) ^ 2 + 2 * ((4771090031 / 1000000000000000000)) * ((191284821 / 500000000000000000))) +
          6 * ((795858243 / 500000000000000000)) * ((191284821 / 500000000000000000)) * (126 / 100) + 8 * ((191284821 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12497) *
          (32 * (((4771090031 / 1000000000000000000) : ℝ) + (795858243 / 500000000000000000) + (191284821 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12497 : ℝ) ^ 16 *
      (d.w0 12497 161 + d.w1 12497 161 * √(π / 2) + 2 * d.w2 12497 161 +
        energyR16 12497 * radiusPolynomialRoot16 (d.w0 12497 161) (d.w1 12497 161)
          (d.w2 12497 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12497 : ℝ) ^ 16 *
        (((1923998153 / 100000000000000000000) : ℝ) + ((1368887943 / 100000000000000000000)) * (126 / 100) + 2 * ((500157651 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12497) *
          (32 * (((1923998153 / 100000000000000000000) : ℝ) + (1368887943 / 100000000000000000000) + (500157651 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12497

/-! A coarse bound on the actual paper statistics constant at dimension 12498. -/
namespace BstLean.Part266.Row12498
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12496 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12496 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12496 128 ≤ (12750 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12750 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12498) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12498 : ℕ))
    (by norm_num : (12498 : ℕ) ≤ 16384)
  have ht : paperTail256 12498 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12498 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12498 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12498 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12498 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12498 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12496 128 * √(2 / (12498 : ℝ)) *
      (√(12498 : ℝ) + paperT0 12498 + paperTail256 12498) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12498 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12498 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12498 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12496 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12496 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12498 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12498

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12498
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12498 (61 / 100) 161 (17 / (100 * 12498)) (26 / (10 * 12498)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12498 (61 / 100) 161 (17 / (100 * 12498)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (500031957 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1600358343 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5819631263 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12498 / 12498 * (61 / 100)) ^ 4 * inverseRadius8 (12498 - 1) /
            envelopeGap 12498 (61 / 100) 161 (17 / (100 * 12498)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12498

namespace BstLean.Part266.Row12498
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12498 161 ≤ (477013731 / 100000000000000000)
  f1 : (tableEnvelope C).f1 12498 161 ≤ (1591398473 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (191246581 / 500000000000000000)
  w0 : (tableEnvelope C).w0 12498 161 ≤ (961768337 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 12498 161 ≤ (136855953 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 12498 161 ≤ (100007519 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (500031957 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (500031957 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1600358343 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5819631263 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((230507 / 62500000) : ℝ) ≤ √(17 / (100 * 12498) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12498) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (447227887 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (40004479037 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12498) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12498) ≤ (11315519 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12498) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12498 * (161 : ℝ) ^ 2 + 26 / (10 * 12498) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12498) : ℝ)) (tA 12498 * 161 ^ 2 + 26 / (10 * 12498)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((230507 / 62500000))) * ((500031957 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((230507 / 62500000)) ^ 3) * ((1600358343 / 1000000000000000000000000))) + ((5819631263 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((230507 / 62500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12498) : ℝ)) d.D d.V d.P (√(tA 12498) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((230507 / 62500000)) ^ 2 * (((447227887 / 200000000000000)) * ((40004479037 / 1000000000000000000)))) + ((5819631263 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12498) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((230507 / 62500000)) * ((500031957 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12498) : ℝ)) (tA 12498 * 161 ^ 2 + 26 / (10 * 12498)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((500031957 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((230507 / 62500000)) ^ 2) * ((1600358343 / 1000000000000000000000000)) + ((5819631263 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12498) : ℝ)) (√(26 / (10 * 12498) : ℝ)) d.D d.V d.P (√(tA 12498) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((230507 / 62500000)) * (((447227887 / 200000000000000)) * ((40004479037 / 1000000000000000000))) + ((5819631263 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12498) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((500031957 / 100000000000000000000) : ℝ) + ((5819631263 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12498

namespace BstLean.Part266.Row12498
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12498 161 ∧
    0 ≤ (tableEnvelope C).f1 12498 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12498 161 ∧
    0 ≤ (tableEnvelope C).w1 12498 161 ∧ 0 ≤ (tableEnvelope C).w2 12498 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12498 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12498 161 ∧ 0 ≤ d.f1 12498 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12498 161 ∧ 0 ≤ d.w1 12498 161 ∧ 0 ≤ d.w2 12498 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12498 ≤ 2 * (228 / 100 : ℝ) / 12498 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12498 ≤ 2 * (370 / 100 : ℝ) / 12498 := by
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
    (completeRAData (tableEnvelope C) 12498 161).locationBound 12498 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12498 161).energyBound 12498 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12498 161) (d.f1 12498 161) d.f2 ≤
      32 * (((477013731 / 100000000000000000) : ℝ) + (1591398473 / 1000000000000000000) + (191246581 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12498 161) (d.w1 12498 161)
      (d.w2 12498 161) ≤
      32 * (((961768337 / 50000000000000000000) : ℝ) + (136855953 / 10000000000000000000) + (100007519 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12498 161) (d.f1 12498 161) d.f2 ≤
      ((477013731 / 100000000000000000) : ℝ) ^ 2 + 2 * ((477013731 / 100000000000000000)) * ((1591398473 / 1000000000000000000)) * (126 / 100) +
      2 * (((1591398473 / 1000000000000000000)) ^ 2 + 2 * ((477013731 / 100000000000000000)) * ((191246581 / 500000000000000000))) +
      6 * ((1591398473 / 1000000000000000000)) * ((191246581 / 500000000000000000)) * (126 / 100) + 8 * ((191246581 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12498 161) (d.f1 12498 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12498 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12498 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12498 161) (d.f1 12498 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12498 161) (d.w1 12498 161) (d.w2 12498 161)
  have hwexpr0 : 0 ≤ d.w0 12498 161 + d.w1 12498 161 * √(π / 2) +
      2 * d.w2 12498 161 + energyR16 12498 *
      radiusPolynomialRoot16 (d.w0 12498 161) (d.w1 12498 161) (d.w2 12498 161) := by
    positivity
  constructor
  · change (12498 : ℝ) ^ 8 * (mA 12498 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12498 161) (d.f1 12498 161) d.f2 + locationR16 12498 *
        radiusPolynomialRoot16 (d.f0 12498 161) (d.f1 12498 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12498 : ℝ) ^ 8 * (mA 12498 : ℝ) ^ 8 *
        ((((477013731 / 100000000000000000) : ℝ) ^ 2 + 2 * ((477013731 / 100000000000000000)) * ((1591398473 / 1000000000000000000)) * (126 / 100) +
          2 * (((1591398473 / 1000000000000000000)) ^ 2 + 2 * ((477013731 / 100000000000000000)) * ((191246581 / 500000000000000000))) +
          6 * ((1591398473 / 1000000000000000000)) * ((191246581 / 500000000000000000)) * (126 / 100) + 8 * ((191246581 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12498) *
          (32 * (((477013731 / 100000000000000000) : ℝ) + (1591398473 / 1000000000000000000) + (191246581 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12498 : ℝ) ^ 16 *
      (d.w0 12498 161 + d.w1 12498 161 * √(π / 2) + 2 * d.w2 12498 161 +
        energyR16 12498 * radiusPolynomialRoot16 (d.w0 12498 161) (d.w1 12498 161)
          (d.w2 12498 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12498 : ℝ) ^ 16 *
        (((961768337 / 50000000000000000000) : ℝ) + ((136855953 / 10000000000000000000)) * (126 / 100) + 2 * ((100007519 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12498) *
          (32 * (((961768337 / 50000000000000000000) : ℝ) + (136855953 / 10000000000000000000) + (100007519 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12498

/-! A coarse bound on the actual paper statistics constant at dimension 12499. -/
namespace BstLean.Part266.Row12499
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 12497 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (12497 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 12497 128 ≤ (12751 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (12751 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 12499) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (12499 : ℕ))
    (by norm_num : (12499 : ℕ) ≤ 16384)
  have ht : paperTail256 12499 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(12499 : ℝ) ≤ 112 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (12499 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 12499 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 12499 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 12499 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16) := by
    change exactRadius 12497 128 * √(2 / (12499 : ℝ)) *
      (√(12499 : ℝ) + paperT0 12499 + paperTail256 12499) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 12499 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 12499 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (12499 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 12497 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (12497 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 12499 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (112 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row12499

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row12499
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 12499 (61 / 100) 161 (17 / (100 * 12499)) (26 / (10 * 12499)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 12499 (61 / 100) 161 (17 / (100 * 12499)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (499911943 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1599846229 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (5815870907 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 12499 / 12499 * (61 / 100)) ^ 4 * inverseRadius8 (12499 - 1) /
            envelopeGap 12499 (61 / 100) 161 (17 / (100 * 12499)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row12499

namespace BstLean.Part266.Row12499
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12499 161 ≤ (4769181191 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 12499 161 ≤ (795539851 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (382416601 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 12499 161 ≤ (240384323 / 12500000000000000000)
  w1 : (tableEnvelope C).w1 12499 161 ≤ (684115429 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 12499 161 ≤ (499917577 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (499911943 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (499911943 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1599846229 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (5815870907 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((737593 / 200000000) : ℝ) ≤ √(17 / (100 * 12499) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12499) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (558967767 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (39998077817 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12499) * 161 ≤ 186 / 10000 := by
    have hs : √(tA 12499) ≤ (113146137 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12499) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12499 * (161 : ℝ) ^ 2 + 26 / (10 * 12499) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12499) : ℝ)) (tA 12499 * 161 ^ 2 + 26 / (10 * 12499)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((737593 / 200000000))) * ((499911943 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((737593 / 200000000)) ^ 3) * ((1599846229 / 1000000000000000000000000))) + ((5815870907 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((737593 / 200000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 12499) : ℝ)) d.D d.V d.P (√(tA 12499) * 161) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((737593 / 200000000)) ^ 2 * (((558967767 / 250000000000000)) * ((39998077817 / 1000000000000000000)))) + ((5815870907 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 12499) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((737593 / 200000000)) * ((499911943 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 12499) : ℝ)) (tA 12499 * 161 ^ 2 + 26 / (10 * 12499)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((499911943 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((737593 / 200000000)) ^ 2) * ((1599846229 / 1000000000000000000000000)) + ((5815870907 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 12499) : ℝ)) (√(26 / (10 * 12499) : ℝ)) d.D d.V d.P (√(tA 12499) * 161) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((737593 / 200000000)) * (((558967767 / 250000000000000)) * ((39998077817 / 1000000000000000000))) + ((5815870907 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 12499) * 161) ≤ _
    unfold AW2
    calc
      _ ≤ ((499911943 / 100000000000000000000) : ℝ) + ((5815870907 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row12499

namespace BstLean.Part266.Row12499
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 12499 161 ∧
    0 ≤ (tableEnvelope C).f1 12499 161 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 12499 161 ∧
    0 ≤ (tableEnvelope C).w1 12499 161 ∧ 0 ≤ (tableEnvelope C).w2 12499 161 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 12499 * (161 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 12499 161 ∧ 0 ≤ d.f1 12499 161 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 12499 161 ∧ 0 ≤ d.w1 12499 161 ∧ 0 ≤ d.w2 12499 161
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 12499 ≤ 2 * (228 / 100 : ℝ) / 12499 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 12499 ≤ 2 * (370 / 100 : ℝ) / 12499 := by
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
    (completeRAData (tableEnvelope C) 12499 161).locationBound 12499 161 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 12499 161).energyBound 12499 161 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 12499 161) (d.f1 12499 161) d.f2 ≤
      32 * (((4769181191 / 1000000000000000000) : ℝ) + (795539851 / 500000000000000000) + (382416601 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 12499 161) (d.w1 12499 161)
      (d.w2 12499 161) ≤
      32 * (((240384323 / 12500000000000000000) : ℝ) + (684115429 / 50000000000000000000) + (499917577 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 12499 161) (d.f1 12499 161) d.f2 ≤
      ((4769181191 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4769181191 / 1000000000000000000)) * ((795539851 / 500000000000000000)) * (126 / 100) +
      2 * (((795539851 / 500000000000000000)) ^ 2 + 2 * ((4769181191 / 1000000000000000000)) * ((382416601 / 1000000000000000000))) +
      6 * ((795539851 / 500000000000000000)) * ((382416601 / 1000000000000000000)) * (126 / 100) + 8 * ((382416601 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 12499 161) (d.f1 12499 161) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 12499 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 12499 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 12499 161) (d.f1 12499 161) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 12499 161) (d.w1 12499 161) (d.w2 12499 161)
  have hwexpr0 : 0 ≤ d.w0 12499 161 + d.w1 12499 161 * √(π / 2) +
      2 * d.w2 12499 161 + energyR16 12499 *
      radiusPolynomialRoot16 (d.w0 12499 161) (d.w1 12499 161) (d.w2 12499 161) := by
    positivity
  constructor
  · change (12499 : ℝ) ^ 8 * (mA 12499 : ℝ) ^ 8 *
      (collectedSecond (d.f0 12499 161) (d.f1 12499 161) d.f2 + locationR16 12499 *
        radiusPolynomialRoot16 (d.f0 12499 161) (d.f1 12499 161) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12499 : ℝ) ^ 8 * (mA 12499 : ℝ) ^ 8 *
        ((((4769181191 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4769181191 / 1000000000000000000)) * ((795539851 / 500000000000000000)) * (126 / 100) +
          2 * (((795539851 / 500000000000000000)) ^ 2 + 2 * ((4769181191 / 1000000000000000000)) * ((382416601 / 1000000000000000000))) +
          6 * ((795539851 / 500000000000000000)) * ((382416601 / 1000000000000000000)) * (126 / 100) + 8 * ((382416601 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 12499) *
          (32 * (((4769181191 / 1000000000000000000) : ℝ) + (795539851 / 500000000000000000) + (382416601 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 12499 : ℝ) ^ 16 *
      (d.w0 12499 161 + d.w1 12499 161 * √(π / 2) + 2 * d.w2 12499 161 +
        energyR16 12499 * radiusPolynomialRoot16 (d.w0 12499 161) (d.w1 12499 161)
          (d.w2 12499 161)) ^ 16 ≤ _
    calc
      _ ≤ (mA 12499 : ℝ) ^ 16 *
        (((240384323 / 12500000000000000000) : ℝ) + ((684115429 / 50000000000000000000)) * (126 / 100) + 2 * ((499917577 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 12499) *
          (32 * (((240384323 / 12500000000000000000) : ℝ) + (684115429 / 50000000000000000000) + (499917577 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row12499
