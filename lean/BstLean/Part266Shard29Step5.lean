import BstLean.Part266Shard29Step4


/-! A coarse bound on the actual paper statistics constant at dimension 13075. -/
namespace BstLean.Part266.Row13075
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13073 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13073 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13073 128 ≤ (13327 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13327 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13075) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13075 : ℕ))
    (by norm_num : (13075 : ℕ) ≤ 16384)
  have ht : paperTail256 13075 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13075 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13075 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13075 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13075 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13075 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13073 128 * √(2 / (13075 : ℝ)) *
      (√(13075 : ℝ) + paperT0 13075 + paperTail256 13075) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13075 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13075 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13075 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13073 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13073 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13075 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13075

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13075
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13075 (61 / 100) 165 (17 / (100 * 13075)) (26 / (10 * 13075)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13075 (61 / 100) 165 (17 / (100 * 13075)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (218354007 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1336009239 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1012320653 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13075 / 13075 * (61 / 100)) ^ 4 * inverseRadius8 (13075 - 1) /
            envelopeGap 13075 (61 / 100) 165 (17 / (100 * 13075)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13075

namespace BstLean.Part266.Row13075
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13075 165 ≤ (2130564679 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13075 165 ≤ (710792433 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (42709809 / 125000000000000000)
  w0 : (tableEnvelope C).w0 13075 165 ≤ (1679939877 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13075 165 ≤ (597622571 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13075 165 ≤ (436711937 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (218354007 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (218354007 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1336009239 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1012320653 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((450727 / 125000000) : ℝ) ≤ √(17 / (100 * 13075) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13075) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2089756001 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36551460149 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13075) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13075) ≤ (2163233 / 20000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13075) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13075 * (165 : ℝ) ^ 2 + 26 / (10 * 13075) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13075) : ℝ)) (tA 13075 * 165 ^ 2 + 26 / (10 * 13075)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((450727 / 125000000))) * ((218354007 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((450727 / 125000000)) ^ 3) * ((1336009239 / 1000000000000000000000000))) + ((1012320653 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((450727 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13075) : ℝ)) d.D d.V d.P (√(tA 13075) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((450727 / 125000000)) ^ 2 * (((2089756001 / 1000000000000000)) * ((36551460149 / 1000000000000000000)))) + ((1012320653 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13075) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((450727 / 125000000)) * ((218354007 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13075) : ℝ)) (tA 13075 * 165 ^ 2 + 26 / (10 * 13075)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((218354007 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((450727 / 125000000)) ^ 2) * ((1336009239 / 1000000000000000000000000)) + ((1012320653 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13075) : ℝ)) (√(26 / (10 * 13075) : ℝ)) d.D d.V d.P (√(tA 13075) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((450727 / 125000000)) * (((2089756001 / 1000000000000000)) * ((36551460149 / 1000000000000000000))) + ((1012320653 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13075) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((218354007 / 50000000000000000000) : ℝ) + ((1012320653 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13075

namespace BstLean.Part266.Row13075
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13075 165 ∧
    0 ≤ (tableEnvelope C).f1 13075 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13075 165 ∧
    0 ≤ (tableEnvelope C).w1 13075 165 ∧ 0 ≤ (tableEnvelope C).w2 13075 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13075 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13075 165 ∧ 0 ≤ d.f1 13075 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13075 165 ∧ 0 ≤ d.w1 13075 165 ∧ 0 ≤ d.w2 13075 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13075 ≤ 2 * (228 / 100 : ℝ) / 13075 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13075 ≤ 2 * (370 / 100 : ℝ) / 13075 := by
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
    (completeRAData (tableEnvelope C) 13075 165).locationBound 13075 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13075 165).energyBound 13075 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13075 165) (d.f1 13075 165) d.f2 ≤
      32 * (((2130564679 / 500000000000000000) : ℝ) + (710792433 / 500000000000000000) + (42709809 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13075 165) (d.w1 13075 165)
      (d.w2 13075 165) ≤
      32 * (((1679939877 / 100000000000000000000) : ℝ) + (597622571 / 50000000000000000000) + (436711937 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13075 165) (d.f1 13075 165) d.f2 ≤
      ((2130564679 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2130564679 / 500000000000000000)) * ((710792433 / 500000000000000000)) * (126 / 100) +
      2 * (((710792433 / 500000000000000000)) ^ 2 + 2 * ((2130564679 / 500000000000000000)) * ((42709809 / 125000000000000000))) +
      6 * ((710792433 / 500000000000000000)) * ((42709809 / 125000000000000000)) * (126 / 100) + 8 * ((42709809 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13075 165) (d.f1 13075 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13075 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13075 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13075 165) (d.f1 13075 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13075 165) (d.w1 13075 165) (d.w2 13075 165)
  have hwexpr0 : 0 ≤ d.w0 13075 165 + d.w1 13075 165 * √(π / 2) +
      2 * d.w2 13075 165 + energyR16 13075 *
      radiusPolynomialRoot16 (d.w0 13075 165) (d.w1 13075 165) (d.w2 13075 165) := by
    positivity
  constructor
  · change (13075 : ℝ) ^ 8 * (mA 13075 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13075 165) (d.f1 13075 165) d.f2 + locationR16 13075 *
        radiusPolynomialRoot16 (d.f0 13075 165) (d.f1 13075 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13075 : ℝ) ^ 8 * (mA 13075 : ℝ) ^ 8 *
        ((((2130564679 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2130564679 / 500000000000000000)) * ((710792433 / 500000000000000000)) * (126 / 100) +
          2 * (((710792433 / 500000000000000000)) ^ 2 + 2 * ((2130564679 / 500000000000000000)) * ((42709809 / 125000000000000000))) +
          6 * ((710792433 / 500000000000000000)) * ((42709809 / 125000000000000000)) * (126 / 100) + 8 * ((42709809 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13075) *
          (32 * (((2130564679 / 500000000000000000) : ℝ) + (710792433 / 500000000000000000) + (42709809 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13075 : ℝ) ^ 16 *
      (d.w0 13075 165 + d.w1 13075 165 * √(π / 2) + 2 * d.w2 13075 165 +
        energyR16 13075 * radiusPolynomialRoot16 (d.w0 13075 165) (d.w1 13075 165)
          (d.w2 13075 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13075 : ℝ) ^ 16 *
        (((1679939877 / 100000000000000000000) : ℝ) + ((597622571 / 50000000000000000000)) * (126 / 100) + 2 * ((436711937 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13075) *
          (32 * (((1679939877 / 100000000000000000000) : ℝ) + (597622571 / 50000000000000000000) + (436711937 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13075

/-! A coarse bound on the actual paper statistics constant at dimension 13076. -/
namespace BstLean.Part266.Row13076
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13074 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13074 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13074 128 ≤ (13328 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13328 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13076) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13076 : ℕ))
    (by norm_num : (13076 : ℕ) ≤ 16384)
  have ht : paperTail256 13076 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13076 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13076 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13076 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13076 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13076 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13074 128 * √(2 / (13076 : ℝ)) *
      (√(13076 : ℝ) + paperT0 13076 + paperTail256 13076) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13076 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13076 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13076 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13074 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13074 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13076 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13076

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13076
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13076 (61 / 100) 165 (17 / (100 * 13076)) (26 / (10 * 13076)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13076 (61 / 100) 165 (17 / (100 * 13076)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (27287989 / 6250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (66780029 / 50000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4046782579 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13076 / 13076 * (61 / 100)) ^ 4 * inverseRadius8 (13076 - 1) /
            envelopeGap 13076 (61 / 100) 165 (17 / (100 * 13076)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13076

namespace BstLean.Part266.Row13076
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13076 165 ≤ (2130157537 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13076 165 ≤ (710656583 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (170806579 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13076 165 ≤ (104972159 / 6250000000000000000)
  w1 : (tableEnvelope C).w1 13076 165 ≤ (597485483 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13076 165 ≤ (87322349 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (27287989 / 6250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (27287989 / 6250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (66780029 / 50000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4046782579 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1802839 / 500000000) : ℝ) ≤ √(17 / (100 * 13076) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13076) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (208951627 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7309173907 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13076) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13076) ≤ (54076689 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13076) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13076 * (165 : ℝ) ^ 2 + 26 / (10 * 13076) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13076) : ℝ)) (tA 13076 * 165 ^ 2 + 26 / (10 * 13076)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1802839 / 500000000))) * ((27287989 / 6250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1802839 / 500000000)) ^ 3) * ((66780029 / 50000000000000000000000))) + ((4046782579 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1802839 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13076) : ℝ)) d.D d.V d.P (√(tA 13076) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1802839 / 500000000)) ^ 2 * (((208951627 / 100000000000000)) * ((7309173907 / 200000000000000000)))) + ((4046782579 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13076) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1802839 / 500000000)) * ((27287989 / 6250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13076) : ℝ)) (tA 13076 * 165 ^ 2 + 26 / (10 * 13076)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((27287989 / 6250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1802839 / 500000000)) ^ 2) * ((66780029 / 50000000000000000000000)) + ((4046782579 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13076) : ℝ)) (√(26 / (10 * 13076) : ℝ)) d.D d.V d.P (√(tA 13076) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1802839 / 500000000)) * (((208951627 / 100000000000000)) * ((7309173907 / 200000000000000000))) + ((4046782579 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13076) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((27287989 / 6250000000000000000) : ℝ) + ((4046782579 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13076

namespace BstLean.Part266.Row13076
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13076 165 ∧
    0 ≤ (tableEnvelope C).f1 13076 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13076 165 ∧
    0 ≤ (tableEnvelope C).w1 13076 165 ∧ 0 ≤ (tableEnvelope C).w2 13076 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13076 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13076 165 ∧ 0 ≤ d.f1 13076 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13076 165 ∧ 0 ≤ d.w1 13076 165 ∧ 0 ≤ d.w2 13076 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13076 ≤ 2 * (228 / 100 : ℝ) / 13076 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13076 ≤ 2 * (370 / 100 : ℝ) / 13076 := by
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
    (completeRAData (tableEnvelope C) 13076 165).locationBound 13076 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13076 165).energyBound 13076 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13076 165) (d.f1 13076 165) d.f2 ≤
      32 * (((2130157537 / 500000000000000000) : ℝ) + (710656583 / 500000000000000000) + (170806579 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13076 165) (d.w1 13076 165)
      (d.w2 13076 165) ≤
      32 * (((104972159 / 6250000000000000000) : ℝ) + (597485483 / 50000000000000000000) + (87322349 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13076 165) (d.f1 13076 165) d.f2 ≤
      ((2130157537 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2130157537 / 500000000000000000)) * ((710656583 / 500000000000000000)) * (126 / 100) +
      2 * (((710656583 / 500000000000000000)) ^ 2 + 2 * ((2130157537 / 500000000000000000)) * ((170806579 / 500000000000000000))) +
      6 * ((710656583 / 500000000000000000)) * ((170806579 / 500000000000000000)) * (126 / 100) + 8 * ((170806579 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13076 165) (d.f1 13076 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13076 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13076 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13076 165) (d.f1 13076 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13076 165) (d.w1 13076 165) (d.w2 13076 165)
  have hwexpr0 : 0 ≤ d.w0 13076 165 + d.w1 13076 165 * √(π / 2) +
      2 * d.w2 13076 165 + energyR16 13076 *
      radiusPolynomialRoot16 (d.w0 13076 165) (d.w1 13076 165) (d.w2 13076 165) := by
    positivity
  constructor
  · change (13076 : ℝ) ^ 8 * (mA 13076 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13076 165) (d.f1 13076 165) d.f2 + locationR16 13076 *
        radiusPolynomialRoot16 (d.f0 13076 165) (d.f1 13076 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13076 : ℝ) ^ 8 * (mA 13076 : ℝ) ^ 8 *
        ((((2130157537 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2130157537 / 500000000000000000)) * ((710656583 / 500000000000000000)) * (126 / 100) +
          2 * (((710656583 / 500000000000000000)) ^ 2 + 2 * ((2130157537 / 500000000000000000)) * ((170806579 / 500000000000000000))) +
          6 * ((710656583 / 500000000000000000)) * ((170806579 / 500000000000000000)) * (126 / 100) + 8 * ((170806579 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13076) *
          (32 * (((2130157537 / 500000000000000000) : ℝ) + (710656583 / 500000000000000000) + (170806579 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13076 : ℝ) ^ 16 *
      (d.w0 13076 165 + d.w1 13076 165 * √(π / 2) + 2 * d.w2 13076 165 +
        energyR16 13076 * radiusPolynomialRoot16 (d.w0 13076 165) (d.w1 13076 165)
          (d.w2 13076 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13076 : ℝ) ^ 16 *
        (((104972159 / 6250000000000000000) : ℝ) + ((597485483 / 50000000000000000000)) * (126 / 100) + 2 * ((87322349 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13076) *
          (32 * (((104972159 / 6250000000000000000) : ℝ) + (597485483 / 50000000000000000000) + (87322349 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13076

/-! A coarse bound on the actual paper statistics constant at dimension 13077. -/
namespace BstLean.Part266.Row13077
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13075 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13075 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13075 128 ≤ (13329 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13329 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13077) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13077 : ℕ))
    (by norm_num : (13077 : ℕ) ≤ 16384)
  have ht : paperTail256 13077 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13077 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13077 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13077 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13077 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13077 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13075 128 * √(2 / (13077 : ℝ)) *
      (√(13077 : ℝ) + paperT0 13077 + paperTail256 13077) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13077 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13077 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13077 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13075 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13075 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13077 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13077

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13077
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13077 (61 / 100) 165 (17 / (100 * 13077)) (26 / (10 * 13077)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13077 (61 / 100) 165 (17 / (100 * 13077)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (27281729 / 6250000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1335192077 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1011071071 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13077 / 13077 * (61 / 100)) ^ 4 * inverseRadius8 (13077 - 1) /
            envelopeGap 13077 (61 / 100) 165 (17 / (100 * 13077)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13077

namespace BstLean.Part266.Row13077
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13077 165 ≤ (212975053 / 50000000000000000)
  f1 : (tableEnvelope C).f1 13077 165 ≤ (28420831 / 20000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (170773931 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13077 165 ≤ (839584669 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13077 165 ≤ (597348439 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13077 165 ≤ (218255791 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (27281729 / 6250000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (27281729 / 6250000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1335192077 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1011071071 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((180277 / 50000000) : ℝ) ≤ √(17 / (100 * 13077) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13077) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2089276583 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36540280199 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13077) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13077) ≤ (108145107 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13077) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13077 * (165 : ℝ) ^ 2 + 26 / (10 * 13077) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13077) : ℝ)) (tA 13077 * 165 ^ 2 + 26 / (10 * 13077)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((180277 / 50000000))) * ((27281729 / 6250000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((180277 / 50000000)) ^ 3) * ((1335192077 / 1000000000000000000000000))) + ((1011071071 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((180277 / 50000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13077) : ℝ)) d.D d.V d.P (√(tA 13077) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((180277 / 50000000)) ^ 2 * (((2089276583 / 1000000000000000)) * ((36540280199 / 1000000000000000000)))) + ((1011071071 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13077) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((180277 / 50000000)) * ((27281729 / 6250000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13077) : ℝ)) (tA 13077 * 165 ^ 2 + 26 / (10 * 13077)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((27281729 / 6250000000000000000) : ℝ) + (24198 / 100000) / (2 * ((180277 / 50000000)) ^ 2) * ((1335192077 / 1000000000000000000000000)) + ((1011071071 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13077) : ℝ)) (√(26 / (10 * 13077) : ℝ)) d.D d.V d.P (√(tA 13077) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((180277 / 50000000)) * (((2089276583 / 1000000000000000)) * ((36540280199 / 1000000000000000000))) + ((1011071071 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13077) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((27281729 / 6250000000000000000) : ℝ) + ((1011071071 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13077

namespace BstLean.Part266.Row13077
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13077 165 ∧
    0 ≤ (tableEnvelope C).f1 13077 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13077 165 ∧
    0 ≤ (tableEnvelope C).w1 13077 165 ∧ 0 ≤ (tableEnvelope C).w2 13077 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13077 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13077 165 ∧ 0 ≤ d.f1 13077 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13077 165 ∧ 0 ≤ d.w1 13077 165 ∧ 0 ≤ d.w2 13077 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13077 ≤ 2 * (228 / 100 : ℝ) / 13077 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13077 ≤ 2 * (370 / 100 : ℝ) / 13077 := by
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
    (completeRAData (tableEnvelope C) 13077 165).locationBound 13077 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13077 165).energyBound 13077 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13077 165) (d.f1 13077 165) d.f2 ≤
      32 * (((212975053 / 50000000000000000) : ℝ) + (28420831 / 20000000000000000) + (170773931 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13077 165) (d.w1 13077 165)
      (d.w2 13077 165) ≤
      32 * (((839584669 / 50000000000000000000) : ℝ) + (597348439 / 50000000000000000000) + (218255791 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13077 165) (d.f1 13077 165) d.f2 ≤
      ((212975053 / 50000000000000000) : ℝ) ^ 2 + 2 * ((212975053 / 50000000000000000)) * ((28420831 / 20000000000000000)) * (126 / 100) +
      2 * (((28420831 / 20000000000000000)) ^ 2 + 2 * ((212975053 / 50000000000000000)) * ((170773931 / 500000000000000000))) +
      6 * ((28420831 / 20000000000000000)) * ((170773931 / 500000000000000000)) * (126 / 100) + 8 * ((170773931 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13077 165) (d.f1 13077 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13077 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13077 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13077 165) (d.f1 13077 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13077 165) (d.w1 13077 165) (d.w2 13077 165)
  have hwexpr0 : 0 ≤ d.w0 13077 165 + d.w1 13077 165 * √(π / 2) +
      2 * d.w2 13077 165 + energyR16 13077 *
      radiusPolynomialRoot16 (d.w0 13077 165) (d.w1 13077 165) (d.w2 13077 165) := by
    positivity
  constructor
  · change (13077 : ℝ) ^ 8 * (mA 13077 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13077 165) (d.f1 13077 165) d.f2 + locationR16 13077 *
        radiusPolynomialRoot16 (d.f0 13077 165) (d.f1 13077 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13077 : ℝ) ^ 8 * (mA 13077 : ℝ) ^ 8 *
        ((((212975053 / 50000000000000000) : ℝ) ^ 2 + 2 * ((212975053 / 50000000000000000)) * ((28420831 / 20000000000000000)) * (126 / 100) +
          2 * (((28420831 / 20000000000000000)) ^ 2 + 2 * ((212975053 / 50000000000000000)) * ((170773931 / 500000000000000000))) +
          6 * ((28420831 / 20000000000000000)) * ((170773931 / 500000000000000000)) * (126 / 100) + 8 * ((170773931 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13077) *
          (32 * (((212975053 / 50000000000000000) : ℝ) + (28420831 / 20000000000000000) + (170773931 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13077 : ℝ) ^ 16 *
      (d.w0 13077 165 + d.w1 13077 165 * √(π / 2) + 2 * d.w2 13077 165 +
        energyR16 13077 * radiusPolynomialRoot16 (d.w0 13077 165) (d.w1 13077 165)
          (d.w2 13077 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13077 : ℝ) ^ 16 *
        (((839584669 / 50000000000000000000) : ℝ) + ((597348439 / 50000000000000000000)) * (126 / 100) + 2 * ((218255791 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13077) *
          (32 * (((839584669 / 50000000000000000000) : ℝ) + (597348439 / 50000000000000000000) + (218255791 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13077

/-! A coarse bound on the actual paper statistics constant at dimension 13078. -/
namespace BstLean.Part266.Row13078
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13076 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13076 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13076 128 ≤ (13330 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13330 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13078) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13078 : ℕ))
    (by norm_num : (13078 : ℕ) ≤ 16384)
  have ht : paperTail256 13078 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13078 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13078 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13078 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13078 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13078 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13076 128 * √(2 / (13078 : ℝ)) *
      (√(13078 : ℝ) + paperT0 13078 + paperTail256 13078) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13078 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13078 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13078 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13076 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13076 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13078 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13078

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13078
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13078 (61 / 100) 165 (17 / (100 * 13078)) (26 / (10 * 13078)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13078 (61 / 100) 165 (17 / (100 * 13078)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (87281507 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (133478373 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (161671509 / 40000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13078 / 13078 * (61 / 100)) ^ 4 * inverseRadius8 (13078 - 1) /
            envelopeGap 13078 (61 / 100) 165 (17 / (100 * 13078)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13078

namespace BstLean.Part266.Row13078
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13078 165 ≤ (2129343659 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13078 165 ≤ (71038501 / 50000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (68296517 / 200000000000000000)
  w0 : (tableEnvelope C).w0 13078 165 ≤ (1678784261 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13078 165 ≤ (7465143 / 625000000000000000)
  w2 : (tableEnvelope C).w2 13078 165 ≤ (436411451 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (87281507 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (87281507 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (133478373 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (161671509 / 40000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1802701 / 500000000) : ℝ) ≤ √(17 / (100 * 13078) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13078) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (130564809 / 62500000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (2283418259 / 62500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13078) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13078) ≤ (54068419 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13078) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13078 * (165 : ℝ) ^ 2 + 26 / (10 * 13078) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13078) : ℝ)) (tA 13078 * 165 ^ 2 + 26 / (10 * 13078)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1802701 / 500000000))) * ((87281507 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1802701 / 500000000)) ^ 3) * ((133478373 / 100000000000000000000000))) + ((161671509 / 40000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1802701 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13078) : ℝ)) d.D d.V d.P (√(tA 13078) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1802701 / 500000000)) ^ 2 * (((130564809 / 62500000000000)) * ((2283418259 / 62500000000000000)))) + ((161671509 / 40000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13078) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1802701 / 500000000)) * ((87281507 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13078) : ℝ)) (tA 13078 * 165 ^ 2 + 26 / (10 * 13078)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((87281507 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1802701 / 500000000)) ^ 2) * ((133478373 / 100000000000000000000000)) + ((161671509 / 40000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13078) : ℝ)) (√(26 / (10 * 13078) : ℝ)) d.D d.V d.P (√(tA 13078) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1802701 / 500000000)) * (((130564809 / 62500000000000)) * ((2283418259 / 62500000000000000))) + ((161671509 / 40000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13078) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((87281507 / 20000000000000000000) : ℝ) + ((161671509 / 40000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13078

namespace BstLean.Part266.Row13078
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13078 165 ∧
    0 ≤ (tableEnvelope C).f1 13078 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13078 165 ∧
    0 ≤ (tableEnvelope C).w1 13078 165 ∧ 0 ≤ (tableEnvelope C).w2 13078 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13078 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13078 165 ∧ 0 ≤ d.f1 13078 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13078 165 ∧ 0 ≤ d.w1 13078 165 ∧ 0 ≤ d.w2 13078 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13078 ≤ 2 * (228 / 100 : ℝ) / 13078 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13078 ≤ 2 * (370 / 100 : ℝ) / 13078 := by
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
    (completeRAData (tableEnvelope C) 13078 165).locationBound 13078 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13078 165).energyBound 13078 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13078 165) (d.f1 13078 165) d.f2 ≤
      32 * (((2129343659 / 500000000000000000) : ℝ) + (71038501 / 50000000000000000) + (68296517 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13078 165) (d.w1 13078 165)
      (d.w2 13078 165) ≤
      32 * (((1678784261 / 100000000000000000000) : ℝ) + (7465143 / 625000000000000000) + (436411451 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13078 165) (d.f1 13078 165) d.f2 ≤
      ((2129343659 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2129343659 / 500000000000000000)) * ((71038501 / 50000000000000000)) * (126 / 100) +
      2 * (((71038501 / 50000000000000000)) ^ 2 + 2 * ((2129343659 / 500000000000000000)) * ((68296517 / 200000000000000000))) +
      6 * ((71038501 / 50000000000000000)) * ((68296517 / 200000000000000000)) * (126 / 100) + 8 * ((68296517 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13078 165) (d.f1 13078 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13078 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13078 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13078 165) (d.f1 13078 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13078 165) (d.w1 13078 165) (d.w2 13078 165)
  have hwexpr0 : 0 ≤ d.w0 13078 165 + d.w1 13078 165 * √(π / 2) +
      2 * d.w2 13078 165 + energyR16 13078 *
      radiusPolynomialRoot16 (d.w0 13078 165) (d.w1 13078 165) (d.w2 13078 165) := by
    positivity
  constructor
  · change (13078 : ℝ) ^ 8 * (mA 13078 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13078 165) (d.f1 13078 165) d.f2 + locationR16 13078 *
        radiusPolynomialRoot16 (d.f0 13078 165) (d.f1 13078 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13078 : ℝ) ^ 8 * (mA 13078 : ℝ) ^ 8 *
        ((((2129343659 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2129343659 / 500000000000000000)) * ((71038501 / 50000000000000000)) * (126 / 100) +
          2 * (((71038501 / 50000000000000000)) ^ 2 + 2 * ((2129343659 / 500000000000000000)) * ((68296517 / 200000000000000000))) +
          6 * ((71038501 / 50000000000000000)) * ((68296517 / 200000000000000000)) * (126 / 100) + 8 * ((68296517 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13078) *
          (32 * (((2129343659 / 500000000000000000) : ℝ) + (71038501 / 50000000000000000) + (68296517 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13078 : ℝ) ^ 16 *
      (d.w0 13078 165 + d.w1 13078 165 * √(π / 2) + 2 * d.w2 13078 165 +
        energyR16 13078 * radiusPolynomialRoot16 (d.w0 13078 165) (d.w1 13078 165)
          (d.w2 13078 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13078 : ℝ) ^ 16 *
        (((1678784261 / 100000000000000000000) : ℝ) + ((7465143 / 625000000000000000)) * (126 / 100) + 2 * ((436411451 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13078) *
          (32 * (((1678784261 / 100000000000000000000) : ℝ) + (7465143 / 625000000000000000) + (436411451 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13078

/-! A coarse bound on the actual paper statistics constant at dimension 13079. -/
namespace BstLean.Part266.Row13079
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13077 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13077 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13077 128 ≤ (13331 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13331 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13079) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13079 : ℕ))
    (by norm_num : (13079 : ℕ) ≤ 16384)
  have ht : paperTail256 13079 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13079 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13079 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13079 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13079 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13079 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13077 128 * √(2 / (13079 : ℝ)) *
      (√(13079 : ℝ) + paperT0 13079 + paperTail256 13079) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13079 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13079 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13079 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13077 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13077 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13079 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13079

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13079
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13079 (61 / 100) 165 (17 / (100 * 13079)) (26 / (10 * 13079)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13079 (61 / 100) 165 (17 / (100 * 13079)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (109076859 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1334375539 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2019646451 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13079 / 13079 * (61 / 100)) ^ 4 * inverseRadius8 (13079 - 1) /
            envelopeGap 13079 (61 / 100) 165 (17 / (100 * 13079)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13079

namespace BstLean.Part266.Row13079
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13079 165 ≤ (4257873847 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13079 165 ≤ (710249287 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (21338583 / 62500000000000000)
  w0 : (tableEnvelope C).w0 13079 165 ≤ (1678399313 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13079 165 ≤ (1194148969 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13079 165 ≤ (436311349 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (109076859 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (109076859 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1334375539 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2019646451 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((225329 / 62500000) : ℝ) ≤ √(17 / (100 * 13079) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13079) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (522199337 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36529105369 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13079) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13079) ≤ (10812857 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13079) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13079 * (165 : ℝ) ^ 2 + 26 / (10 * 13079) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13079) : ℝ)) (tA 13079 * 165 ^ 2 + 26 / (10 * 13079)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((225329 / 62500000))) * ((109076859 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((225329 / 62500000)) ^ 3) * ((1334375539 / 1000000000000000000000000))) + ((2019646451 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((225329 / 62500000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13079) : ℝ)) d.D d.V d.P (√(tA 13079) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((225329 / 62500000)) ^ 2 * (((522199337 / 250000000000000)) * ((36529105369 / 1000000000000000000)))) + ((2019646451 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13079) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((225329 / 62500000)) * ((109076859 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13079) : ℝ)) (tA 13079 * 165 ^ 2 + 26 / (10 * 13079)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((109076859 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((225329 / 62500000)) ^ 2) * ((1334375539 / 1000000000000000000000000)) + ((2019646451 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13079) : ℝ)) (√(26 / (10 * 13079) : ℝ)) d.D d.V d.P (√(tA 13079) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((225329 / 62500000)) * (((522199337 / 250000000000000)) * ((36529105369 / 1000000000000000000))) + ((2019646451 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13079) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((109076859 / 25000000000000000000) : ℝ) + ((2019646451 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13079

namespace BstLean.Part266.Row13079
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13079 165 ∧
    0 ≤ (tableEnvelope C).f1 13079 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13079 165 ∧
    0 ≤ (tableEnvelope C).w1 13079 165 ∧ 0 ≤ (tableEnvelope C).w2 13079 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13079 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13079 165 ∧ 0 ≤ d.f1 13079 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13079 165 ∧ 0 ≤ d.w1 13079 165 ∧ 0 ≤ d.w2 13079 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13079 ≤ 2 * (228 / 100 : ℝ) / 13079 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13079 ≤ 2 * (370 / 100 : ℝ) / 13079 := by
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
    (completeRAData (tableEnvelope C) 13079 165).locationBound 13079 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13079 165).energyBound 13079 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13079 165) (d.f1 13079 165) d.f2 ≤
      32 * (((4257873847 / 1000000000000000000) : ℝ) + (710249287 / 500000000000000000) + (21338583 / 62500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13079 165) (d.w1 13079 165)
      (d.w2 13079 165) ≤
      32 * (((1678399313 / 100000000000000000000) : ℝ) + (1194148969 / 100000000000000000000) + (436311349 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13079 165) (d.f1 13079 165) d.f2 ≤
      ((4257873847 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4257873847 / 1000000000000000000)) * ((710249287 / 500000000000000000)) * (126 / 100) +
      2 * (((710249287 / 500000000000000000)) ^ 2 + 2 * ((4257873847 / 1000000000000000000)) * ((21338583 / 62500000000000000))) +
      6 * ((710249287 / 500000000000000000)) * ((21338583 / 62500000000000000)) * (126 / 100) + 8 * ((21338583 / 62500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13079 165) (d.f1 13079 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13079 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13079 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13079 165) (d.f1 13079 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13079 165) (d.w1 13079 165) (d.w2 13079 165)
  have hwexpr0 : 0 ≤ d.w0 13079 165 + d.w1 13079 165 * √(π / 2) +
      2 * d.w2 13079 165 + energyR16 13079 *
      radiusPolynomialRoot16 (d.w0 13079 165) (d.w1 13079 165) (d.w2 13079 165) := by
    positivity
  constructor
  · change (13079 : ℝ) ^ 8 * (mA 13079 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13079 165) (d.f1 13079 165) d.f2 + locationR16 13079 *
        radiusPolynomialRoot16 (d.f0 13079 165) (d.f1 13079 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13079 : ℝ) ^ 8 * (mA 13079 : ℝ) ^ 8 *
        ((((4257873847 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4257873847 / 1000000000000000000)) * ((710249287 / 500000000000000000)) * (126 / 100) +
          2 * (((710249287 / 500000000000000000)) ^ 2 + 2 * ((4257873847 / 1000000000000000000)) * ((21338583 / 62500000000000000))) +
          6 * ((710249287 / 500000000000000000)) * ((21338583 / 62500000000000000)) * (126 / 100) + 8 * ((21338583 / 62500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13079) *
          (32 * (((4257873847 / 1000000000000000000) : ℝ) + (710249287 / 500000000000000000) + (21338583 / 62500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13079 : ℝ) ^ 16 *
      (d.w0 13079 165 + d.w1 13079 165 * √(π / 2) + 2 * d.w2 13079 165 +
        energyR16 13079 * radiusPolynomialRoot16 (d.w0 13079 165) (d.w1 13079 165)
          (d.w2 13079 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13079 : ℝ) ^ 16 *
        (((1678399313 / 100000000000000000000) : ℝ) + ((1194148969 / 100000000000000000000)) * (126 / 100) + 2 * ((436311349 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13079) *
          (32 * (((1678399313 / 100000000000000000000) : ℝ) + (1194148969 / 100000000000000000000) + (436311349 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13079

/-! A coarse bound on the actual paper statistics constant at dimension 13080. -/
namespace BstLean.Part266.Row13080
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13078 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13078 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13078 128 ≤ (13332 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13332 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13080) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13080 : ℕ))
    (by norm_num : (13080 : ℕ) ≤ 16384)
  have ht : paperTail256 13080 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13080 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13080 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13080 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13080 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13080 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13078 128 * √(2 / (13080 : ℝ)) *
      (√(13080 : ℝ) + paperT0 13080 + paperTail256 13080) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13080 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13080 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13080 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13078 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13078 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13080 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13080

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13080
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13080 (61 / 100) 165 (17 / (100 * 13080)) (26 / (10 * 13080)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13080 (61 / 100) 165 (17 / (100 * 13080)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (54525921 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (266793501 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4036799813 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13080 / 13080 * (61 / 100)) ^ 4 * inverseRadius8 (13080 - 1) /
            envelopeGap 13080 (61 / 100) 165 (17 / (100 * 13080)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13080

namespace BstLean.Part266.Row13080
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13080 165 ≤ (2128528621 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13080 165 ≤ (710113213 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (170675997 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13080 165 ≤ (335602761 / 20000000000000000000)
  w1 : (tableEnvelope C).w1 13080 165 ≤ (596937409 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13080 165 ≤ (436211279 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (54525921 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (54525921 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (266793501 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4036799813 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3605127 / 1000000000) : ℝ) ≤ √(17 / (100 * 13080) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13080) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (10442789 / 5000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (2282719993 / 62500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13080) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13080) ≤ (108120303 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13080) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13080 * (165 : ℝ) ^ 2 + 26 / (10 * 13080) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13080) : ℝ)) (tA 13080 * 165 ^ 2 + 26 / (10 * 13080)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3605127 / 1000000000))) * ((54525921 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3605127 / 1000000000)) ^ 3) * ((266793501 / 200000000000000000000000))) + ((4036799813 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3605127 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13080) : ℝ)) d.D d.V d.P (√(tA 13080) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3605127 / 1000000000)) ^ 2 * (((10442789 / 5000000000000)) * ((2282719993 / 62500000000000000)))) + ((4036799813 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13080) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3605127 / 1000000000)) * ((54525921 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13080) : ℝ)) (tA 13080 * 165 ^ 2 + 26 / (10 * 13080)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((54525921 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3605127 / 1000000000)) ^ 2) * ((266793501 / 200000000000000000000000)) + ((4036799813 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13080) : ℝ)) (√(26 / (10 * 13080) : ℝ)) d.D d.V d.P (√(tA 13080) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3605127 / 1000000000)) * (((10442789 / 5000000000000)) * ((2282719993 / 62500000000000000))) + ((4036799813 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13080) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((54525921 / 12500000000000000000) : ℝ) + ((4036799813 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13080

namespace BstLean.Part266.Row13080
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13080 165 ∧
    0 ≤ (tableEnvelope C).f1 13080 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13080 165 ∧
    0 ≤ (tableEnvelope C).w1 13080 165 ∧ 0 ≤ (tableEnvelope C).w2 13080 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13080 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13080 165 ∧ 0 ≤ d.f1 13080 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13080 165 ∧ 0 ≤ d.w1 13080 165 ∧ 0 ≤ d.w2 13080 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13080 ≤ 2 * (228 / 100 : ℝ) / 13080 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13080 ≤ 2 * (370 / 100 : ℝ) / 13080 := by
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
    (completeRAData (tableEnvelope C) 13080 165).locationBound 13080 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13080 165).energyBound 13080 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13080 165) (d.f1 13080 165) d.f2 ≤
      32 * (((2128528621 / 500000000000000000) : ℝ) + (710113213 / 500000000000000000) + (170675997 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13080 165) (d.w1 13080 165)
      (d.w2 13080 165) ≤
      32 * (((335602761 / 20000000000000000000) : ℝ) + (596937409 / 50000000000000000000) + (436211279 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13080 165) (d.f1 13080 165) d.f2 ≤
      ((2128528621 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2128528621 / 500000000000000000)) * ((710113213 / 500000000000000000)) * (126 / 100) +
      2 * (((710113213 / 500000000000000000)) ^ 2 + 2 * ((2128528621 / 500000000000000000)) * ((170675997 / 500000000000000000))) +
      6 * ((710113213 / 500000000000000000)) * ((170675997 / 500000000000000000)) * (126 / 100) + 8 * ((170675997 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13080 165) (d.f1 13080 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13080 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13080 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13080 165) (d.f1 13080 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13080 165) (d.w1 13080 165) (d.w2 13080 165)
  have hwexpr0 : 0 ≤ d.w0 13080 165 + d.w1 13080 165 * √(π / 2) +
      2 * d.w2 13080 165 + energyR16 13080 *
      radiusPolynomialRoot16 (d.w0 13080 165) (d.w1 13080 165) (d.w2 13080 165) := by
    positivity
  constructor
  · change (13080 : ℝ) ^ 8 * (mA 13080 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13080 165) (d.f1 13080 165) d.f2 + locationR16 13080 *
        radiusPolynomialRoot16 (d.f0 13080 165) (d.f1 13080 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13080 : ℝ) ^ 8 * (mA 13080 : ℝ) ^ 8 *
        ((((2128528621 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2128528621 / 500000000000000000)) * ((710113213 / 500000000000000000)) * (126 / 100) +
          2 * (((710113213 / 500000000000000000)) ^ 2 + 2 * ((2128528621 / 500000000000000000)) * ((170675997 / 500000000000000000))) +
          6 * ((710113213 / 500000000000000000)) * ((170675997 / 500000000000000000)) * (126 / 100) + 8 * ((170675997 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13080) *
          (32 * (((2128528621 / 500000000000000000) : ℝ) + (710113213 / 500000000000000000) + (170675997 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13080 : ℝ) ^ 16 *
      (d.w0 13080 165 + d.w1 13080 165 * √(π / 2) + 2 * d.w2 13080 165 +
        energyR16 13080 * radiusPolynomialRoot16 (d.w0 13080 165) (d.w1 13080 165)
          (d.w2 13080 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13080 : ℝ) ^ 16 *
        (((335602761 / 20000000000000000000) : ℝ) + ((596937409 / 50000000000000000000)) * (126 / 100) + 2 * ((436211279 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13080) *
          (32 * (((335602761 / 20000000000000000000) : ℝ) + (596937409 / 50000000000000000000) + (436211279 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13080

/-! A coarse bound on the actual paper statistics constant at dimension 13081. -/
namespace BstLean.Part266.Row13081
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13079 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13079 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13079 128 ≤ (13333 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13333 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13081) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13081 : ℕ))
    (by norm_num : (13081 : ℕ) ≤ 16384)
  have ht : paperTail256 13081 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13081 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13081 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13081 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13081 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13081 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13079 128 * √(2 / (13081 : ℝ)) *
      (√(13081 : ℝ) + paperT0 13081 + paperTail256 13081) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13081 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13081 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13081 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13079 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13079 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13081 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13081

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13081
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13081 (61 / 100) 165 (17 / (100 * 13081)) (26 / (10 * 13081)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13081 (61 / 100) 165 (17 / (100 * 13081)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (436107331 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (666779813 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (504288557 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13081 / 13081 * (61 / 100)) ^ 4 * inverseRadius8 (13081 - 1) /
            envelopeGap 13081 (61 / 100) 165 (17 / (100 * 13081)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13081

namespace BstLean.Part266.Row13081
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13081 165 ≤ (851248863 / 200000000000000000)
  f1 : (tableEnvelope C).f1 13081 165 ≤ (88747197 / 62500000000000000)
  f2 : (tableEnvelope C).f2 ≤ (13651471 / 40000000000000000)
  w0 : (tableEnvelope C).w0 13081 165 ≤ (838814557 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13081 165 ≤ (1193601087 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13081 165 ≤ (436111239 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (436107331 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (436107331 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (666779813 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (504288557 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3604989 / 1000000000) : ℝ) ≤ √(17 / (100 * 13081) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13081) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1044159149 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9129483919 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13081) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13081) ≤ (54056019 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13081) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13081 * (165 : ℝ) ^ 2 + 26 / (10 * 13081) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13081) : ℝ)) (tA 13081 * 165 ^ 2 + 26 / (10 * 13081)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3604989 / 1000000000))) * ((436107331 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3604989 / 1000000000)) ^ 3) * ((666779813 / 500000000000000000000000))) + ((504288557 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3604989 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13081) : ℝ)) d.D d.V d.P (√(tA 13081) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3604989 / 1000000000)) ^ 2 * (((1044159149 / 500000000000000)) * ((9129483919 / 250000000000000000)))) + ((504288557 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13081) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3604989 / 1000000000)) * ((436107331 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13081) : ℝ)) (tA 13081 * 165 ^ 2 + 26 / (10 * 13081)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((436107331 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3604989 / 1000000000)) ^ 2) * ((666779813 / 500000000000000000000000)) + ((504288557 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13081) : ℝ)) (√(26 / (10 * 13081) : ℝ)) d.D d.V d.P (√(tA 13081) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3604989 / 1000000000)) * (((1044159149 / 500000000000000)) * ((9129483919 / 250000000000000000))) + ((504288557 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13081) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((436107331 / 100000000000000000000) : ℝ) + ((504288557 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13081

namespace BstLean.Part266.Row13081
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13081 165 ∧
    0 ≤ (tableEnvelope C).f1 13081 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13081 165 ∧
    0 ≤ (tableEnvelope C).w1 13081 165 ∧ 0 ≤ (tableEnvelope C).w2 13081 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13081 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13081 165 ∧ 0 ≤ d.f1 13081 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13081 165 ∧ 0 ≤ d.w1 13081 165 ∧ 0 ≤ d.w2 13081 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13081 ≤ 2 * (228 / 100 : ℝ) / 13081 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13081 ≤ 2 * (370 / 100 : ℝ) / 13081 := by
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
    (completeRAData (tableEnvelope C) 13081 165).locationBound 13081 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13081 165).energyBound 13081 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13081 165) (d.f1 13081 165) d.f2 ≤
      32 * (((851248863 / 200000000000000000) : ℝ) + (88747197 / 62500000000000000) + (13651471 / 40000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13081 165) (d.w1 13081 165)
      (d.w2 13081 165) ≤
      32 * (((838814557 / 50000000000000000000) : ℝ) + (1193601087 / 100000000000000000000) + (436111239 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13081 165) (d.f1 13081 165) d.f2 ≤
      ((851248863 / 200000000000000000) : ℝ) ^ 2 + 2 * ((851248863 / 200000000000000000)) * ((88747197 / 62500000000000000)) * (126 / 100) +
      2 * (((88747197 / 62500000000000000)) ^ 2 + 2 * ((851248863 / 200000000000000000)) * ((13651471 / 40000000000000000))) +
      6 * ((88747197 / 62500000000000000)) * ((13651471 / 40000000000000000)) * (126 / 100) + 8 * ((13651471 / 40000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13081 165) (d.f1 13081 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13081 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13081 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13081 165) (d.f1 13081 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13081 165) (d.w1 13081 165) (d.w2 13081 165)
  have hwexpr0 : 0 ≤ d.w0 13081 165 + d.w1 13081 165 * √(π / 2) +
      2 * d.w2 13081 165 + energyR16 13081 *
      radiusPolynomialRoot16 (d.w0 13081 165) (d.w1 13081 165) (d.w2 13081 165) := by
    positivity
  constructor
  · change (13081 : ℝ) ^ 8 * (mA 13081 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13081 165) (d.f1 13081 165) d.f2 + locationR16 13081 *
        radiusPolynomialRoot16 (d.f0 13081 165) (d.f1 13081 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13081 : ℝ) ^ 8 * (mA 13081 : ℝ) ^ 8 *
        ((((851248863 / 200000000000000000) : ℝ) ^ 2 + 2 * ((851248863 / 200000000000000000)) * ((88747197 / 62500000000000000)) * (126 / 100) +
          2 * (((88747197 / 62500000000000000)) ^ 2 + 2 * ((851248863 / 200000000000000000)) * ((13651471 / 40000000000000000))) +
          6 * ((88747197 / 62500000000000000)) * ((13651471 / 40000000000000000)) * (126 / 100) + 8 * ((13651471 / 40000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13081) *
          (32 * (((851248863 / 200000000000000000) : ℝ) + (88747197 / 62500000000000000) + (13651471 / 40000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13081 : ℝ) ^ 16 *
      (d.w0 13081 165 + d.w1 13081 165 * √(π / 2) + 2 * d.w2 13081 165 +
        energyR16 13081 * radiusPolynomialRoot16 (d.w0 13081 165) (d.w1 13081 165)
          (d.w2 13081 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13081 : ℝ) ^ 16 *
        (((838814557 / 50000000000000000000) : ℝ) + ((1193601087 / 100000000000000000000)) * (126 / 100) + 2 * ((436111239 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13081) *
          (32 * (((838814557 / 50000000000000000000) : ℝ) + (1193601087 / 100000000000000000000) + (436111239 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13081

/-! A coarse bound on the actual paper statistics constant at dimension 13082. -/
namespace BstLean.Part266.Row13082
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13080 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13080 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13080 128 ≤ (13334 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13334 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13082) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13082 : ℕ))
    (by norm_num : (13082 : ℕ) ≤ 16384)
  have ht : paperTail256 13082 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13082 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13082 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13082 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13082 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13082 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13080 128 * √(2 / (13082 : ℝ)) *
      (√(13082 : ℝ) + paperT0 13082 + paperTail256 13082) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13082 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13082 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13082 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13080 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13080 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13082 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13082

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13082
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13082 (61 / 100) 165 (17 / (100 * 13082)) (26 / (10 * 13082)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13082 (61 / 100) 165 (17 / (100 * 13082)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (109001831 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1333151903 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4031818831 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13082 / 13082 * (61 / 100)) ^ 4 * inverseRadius8 (13082 - 1) /
            envelopeGap 13082 (61 / 100) 165 (17 / (100 * 13082)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13082

namespace BstLean.Part266.Row13082
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13082 165 ≤ (4255431659 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13082 165 ≤ (1419683961 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (170610787 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13082 165 ≤ (1677244551 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13082 165 ≤ (298331861 / 25000000000000000000)
  w2 : (tableEnvelope C).w2 13082 165 ≤ (43601123 / 10000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (109001831 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (109001831 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1333151903 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4031818831 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3604851 / 1000000000) : ℝ) ≤ √(17 / (100 * 13082) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13082) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (52201971 / 25000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18256176373 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13082) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13082) ≤ (54051887 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13082) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13082 * (165 : ℝ) ^ 2 + 26 / (10 * 13082) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13082) : ℝ)) (tA 13082 * 165 ^ 2 + 26 / (10 * 13082)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3604851 / 1000000000))) * ((109001831 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3604851 / 1000000000)) ^ 3) * ((1333151903 / 1000000000000000000000000))) + ((4031818831 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3604851 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13082) : ℝ)) d.D d.V d.P (√(tA 13082) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3604851 / 1000000000)) ^ 2 * (((52201971 / 25000000000000)) * ((18256176373 / 500000000000000000)))) + ((4031818831 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13082) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3604851 / 1000000000)) * ((109001831 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13082) : ℝ)) (tA 13082 * 165 ^ 2 + 26 / (10 * 13082)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((109001831 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3604851 / 1000000000)) ^ 2) * ((1333151903 / 1000000000000000000000000)) + ((4031818831 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13082) : ℝ)) (√(26 / (10 * 13082) : ℝ)) d.D d.V d.P (√(tA 13082) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3604851 / 1000000000)) * (((52201971 / 25000000000000)) * ((18256176373 / 500000000000000000))) + ((4031818831 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13082) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((109001831 / 25000000000000000000) : ℝ) + ((4031818831 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13082

namespace BstLean.Part266.Row13082
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13082 165 ∧
    0 ≤ (tableEnvelope C).f1 13082 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13082 165 ∧
    0 ≤ (tableEnvelope C).w1 13082 165 ∧ 0 ≤ (tableEnvelope C).w2 13082 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13082 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13082 165 ∧ 0 ≤ d.f1 13082 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13082 165 ∧ 0 ≤ d.w1 13082 165 ∧ 0 ≤ d.w2 13082 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13082 ≤ 2 * (228 / 100 : ℝ) / 13082 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13082 ≤ 2 * (370 / 100 : ℝ) / 13082 := by
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
    (completeRAData (tableEnvelope C) 13082 165).locationBound 13082 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13082 165).energyBound 13082 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13082 165) (d.f1 13082 165) d.f2 ≤
      32 * (((4255431659 / 1000000000000000000) : ℝ) + (1419683961 / 1000000000000000000) + (170610787 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13082 165) (d.w1 13082 165)
      (d.w2 13082 165) ≤
      32 * (((1677244551 / 100000000000000000000) : ℝ) + (298331861 / 25000000000000000000) + (43601123 / 10000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13082 165) (d.f1 13082 165) d.f2 ≤
      ((4255431659 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4255431659 / 1000000000000000000)) * ((1419683961 / 1000000000000000000)) * (126 / 100) +
      2 * (((1419683961 / 1000000000000000000)) ^ 2 + 2 * ((4255431659 / 1000000000000000000)) * ((170610787 / 500000000000000000))) +
      6 * ((1419683961 / 1000000000000000000)) * ((170610787 / 500000000000000000)) * (126 / 100) + 8 * ((170610787 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13082 165) (d.f1 13082 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13082 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13082 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13082 165) (d.f1 13082 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13082 165) (d.w1 13082 165) (d.w2 13082 165)
  have hwexpr0 : 0 ≤ d.w0 13082 165 + d.w1 13082 165 * √(π / 2) +
      2 * d.w2 13082 165 + energyR16 13082 *
      radiusPolynomialRoot16 (d.w0 13082 165) (d.w1 13082 165) (d.w2 13082 165) := by
    positivity
  constructor
  · change (13082 : ℝ) ^ 8 * (mA 13082 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13082 165) (d.f1 13082 165) d.f2 + locationR16 13082 *
        radiusPolynomialRoot16 (d.f0 13082 165) (d.f1 13082 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13082 : ℝ) ^ 8 * (mA 13082 : ℝ) ^ 8 *
        ((((4255431659 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4255431659 / 1000000000000000000)) * ((1419683961 / 1000000000000000000)) * (126 / 100) +
          2 * (((1419683961 / 1000000000000000000)) ^ 2 + 2 * ((4255431659 / 1000000000000000000)) * ((170610787 / 500000000000000000))) +
          6 * ((1419683961 / 1000000000000000000)) * ((170610787 / 500000000000000000)) * (126 / 100) + 8 * ((170610787 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13082) *
          (32 * (((4255431659 / 1000000000000000000) : ℝ) + (1419683961 / 1000000000000000000) + (170610787 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13082 : ℝ) ^ 16 *
      (d.w0 13082 165 + d.w1 13082 165 * √(π / 2) + 2 * d.w2 13082 165 +
        energyR16 13082 * radiusPolynomialRoot16 (d.w0 13082 165) (d.w1 13082 165)
          (d.w2 13082 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13082 : ℝ) ^ 16 *
        (((1677244551 / 100000000000000000000) : ℝ) + ((298331861 / 25000000000000000000)) * (126 / 100) + 2 * ((43601123 / 10000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13082) *
          (32 * (((1677244551 / 100000000000000000000) : ℝ) + (298331861 / 25000000000000000000) + (43601123 / 10000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13082

/-! A coarse bound on the actual paper statistics constant at dimension 13083. -/
namespace BstLean.Part266.Row13083
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13081 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13081 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13081 128 ≤ (13335 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13335 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13083) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13083 : ℕ))
    (by norm_num : (13083 : ℕ) ≤ 16384)
  have ht : paperTail256 13083 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13083 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13083 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13083 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13083 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13083 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13081 128 * √(2 / (13083 : ℝ)) *
      (√(13083 : ℝ) + paperT0 13083 + paperTail256 13083) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13083 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13083 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13083 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13081 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13081 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13083 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13083

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13083
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13083 (61 / 100) 165 (17 / (100 * 13083)) (26 / (10 * 13083)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13083 (61 / 100) 165 (17 / (100 * 13083)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (108976837 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (83296521 / 62500000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (503666367 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13083 / 13083 * (61 / 100)) ^ 4 * inverseRadius8 (13083 - 1) /
            envelopeGap 13083 (61 / 100) 165 (17 / (100 * 13083)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13083

namespace BstLean.Part266.Row13083
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13083 165 ≤ (170184771 / 40000000000000000)
  f1 : (tableEnvelope C).f1 13083 165 ≤ (177426607 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (42644549 / 125000000000000000)
  w0 : (tableEnvelope C).w0 13083 165 ≤ (838430059 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13083 165 ≤ (119305389 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 13083 165 ≤ (108977813 / 25000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (108976837 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (108976837 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (83296521 / 62500000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (503666367 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3604713 / 1000000000) : ℝ) ≤ √(17 / (100 * 13083) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13083) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2087839429 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18253385549 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13083) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13083) ≤ (108095511 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13083) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13083 * (165 : ℝ) ^ 2 + 26 / (10 * 13083) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13083) : ℝ)) (tA 13083 * 165 ^ 2 + 26 / (10 * 13083)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3604713 / 1000000000))) * ((108976837 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3604713 / 1000000000)) ^ 3) * ((83296521 / 62500000000000000000000))) + ((503666367 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3604713 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13083) : ℝ)) d.D d.V d.P (√(tA 13083) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3604713 / 1000000000)) ^ 2 * (((2087839429 / 1000000000000000)) * ((18253385549 / 500000000000000000)))) + ((503666367 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13083) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3604713 / 1000000000)) * ((108976837 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13083) : ℝ)) (tA 13083 * 165 ^ 2 + 26 / (10 * 13083)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((108976837 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3604713 / 1000000000)) ^ 2) * ((83296521 / 62500000000000000000000)) + ((503666367 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13083) : ℝ)) (√(26 / (10 * 13083) : ℝ)) d.D d.V d.P (√(tA 13083) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3604713 / 1000000000)) * (((2087839429 / 1000000000000000)) * ((18253385549 / 500000000000000000))) + ((503666367 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13083) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((108976837 / 25000000000000000000) : ℝ) + ((503666367 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13083

namespace BstLean.Part266.Row13083
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13083 165 ∧
    0 ≤ (tableEnvelope C).f1 13083 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13083 165 ∧
    0 ≤ (tableEnvelope C).w1 13083 165 ∧ 0 ≤ (tableEnvelope C).w2 13083 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13083 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13083 165 ∧ 0 ≤ d.f1 13083 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13083 165 ∧ 0 ≤ d.w1 13083 165 ∧ 0 ≤ d.w2 13083 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13083 ≤ 2 * (228 / 100 : ℝ) / 13083 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13083 ≤ 2 * (370 / 100 : ℝ) / 13083 := by
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
    (completeRAData (tableEnvelope C) 13083 165).locationBound 13083 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13083 165).energyBound 13083 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13083 165) (d.f1 13083 165) d.f2 ≤
      32 * (((170184771 / 40000000000000000) : ℝ) + (177426607 / 125000000000000000) + (42644549 / 125000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13083 165) (d.w1 13083 165)
      (d.w2 13083 165) ≤
      32 * (((838430059 / 50000000000000000000) : ℝ) + (119305389 / 10000000000000000000) + (108977813 / 25000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13083 165) (d.f1 13083 165) d.f2 ≤
      ((170184771 / 40000000000000000) : ℝ) ^ 2 + 2 * ((170184771 / 40000000000000000)) * ((177426607 / 125000000000000000)) * (126 / 100) +
      2 * (((177426607 / 125000000000000000)) ^ 2 + 2 * ((170184771 / 40000000000000000)) * ((42644549 / 125000000000000000))) +
      6 * ((177426607 / 125000000000000000)) * ((42644549 / 125000000000000000)) * (126 / 100) + 8 * ((42644549 / 125000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13083 165) (d.f1 13083 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13083 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13083 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13083 165) (d.f1 13083 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13083 165) (d.w1 13083 165) (d.w2 13083 165)
  have hwexpr0 : 0 ≤ d.w0 13083 165 + d.w1 13083 165 * √(π / 2) +
      2 * d.w2 13083 165 + energyR16 13083 *
      radiusPolynomialRoot16 (d.w0 13083 165) (d.w1 13083 165) (d.w2 13083 165) := by
    positivity
  constructor
  · change (13083 : ℝ) ^ 8 * (mA 13083 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13083 165) (d.f1 13083 165) d.f2 + locationR16 13083 *
        radiusPolynomialRoot16 (d.f0 13083 165) (d.f1 13083 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13083 : ℝ) ^ 8 * (mA 13083 : ℝ) ^ 8 *
        ((((170184771 / 40000000000000000) : ℝ) ^ 2 + 2 * ((170184771 / 40000000000000000)) * ((177426607 / 125000000000000000)) * (126 / 100) +
          2 * (((177426607 / 125000000000000000)) ^ 2 + 2 * ((170184771 / 40000000000000000)) * ((42644549 / 125000000000000000))) +
          6 * ((177426607 / 125000000000000000)) * ((42644549 / 125000000000000000)) * (126 / 100) + 8 * ((42644549 / 125000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13083) *
          (32 * (((170184771 / 40000000000000000) : ℝ) + (177426607 / 125000000000000000) + (42644549 / 125000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13083 : ℝ) ^ 16 *
      (d.w0 13083 165 + d.w1 13083 165 * √(π / 2) + 2 * d.w2 13083 165 +
        energyR16 13083 * radiusPolynomialRoot16 (d.w0 13083 165) (d.w1 13083 165)
          (d.w2 13083 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13083 : ℝ) ^ 16 *
        (((838430059 / 50000000000000000000) : ℝ) + ((119305389 / 10000000000000000000)) * (126 / 100) + 2 * ((108977813 / 25000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13083) *
          (32 * (((838430059 / 50000000000000000000) : ℝ) + (119305389 / 10000000000000000000) + (108977813 / 25000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13083

/-! A coarse bound on the actual paper statistics constant at dimension 13084. -/
namespace BstLean.Part266.Row13084
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13082 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13082 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13082 128 ≤ (13336 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13336 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13084) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13084 : ℕ))
    (by norm_num : (13084 : ℕ) ≤ 16384)
  have ht : paperTail256 13084 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13084 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13084 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13084 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13084 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13084 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13082 128 * √(2 / (13084 : ℝ)) *
      (√(13084 : ℝ) + paperT0 13084 + paperTail256 13084) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13084 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13084 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13084 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13082 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13082 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13084 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13084

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13084
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13084 (61 / 100) 165 (17 / (100 * 13084)) (26 / (10 * 13084)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13084 (61 / 100) 165 (17 / (100 * 13084)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (217903701 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (53293477 / 40000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (402684477 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13084 / 13084 * (61 / 100)) ^ 4 * inverseRadius8 (13084 - 1) /
            envelopeGap 13084 (61 / 100) 165 (17 / (100 * 13084)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13084

namespace BstLean.Part266.Row13084
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13084 165 ≤ (4253803757 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13084 165 ≤ (177392631 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (170545567 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13084 165 ≤ (419118781 / 25000000000000000000)
  w1 : (tableEnvelope C).w1 13084 165 ≤ (238556019 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 13084 165 ≤ (435811303 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (217903701 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (217903701 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (53293477 / 40000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (402684477 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((112643 / 31250000) : ℝ) ≤ √(17 / (100 * 13084) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13084) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2087600063 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7300238147 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13084) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13084) ≤ (108087249 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13084) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13084 * (165 : ℝ) ^ 2 + 26 / (10 * 13084) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13084) : ℝ)) (tA 13084 * 165 ^ 2 + 26 / (10 * 13084)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((112643 / 31250000))) * ((217903701 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((112643 / 31250000)) ^ 3) * ((53293477 / 40000000000000000000000))) + ((402684477 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((112643 / 31250000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13084) : ℝ)) d.D d.V d.P (√(tA 13084) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((112643 / 31250000)) ^ 2 * (((2087600063 / 1000000000000000)) * ((7300238147 / 200000000000000000)))) + ((402684477 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13084) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((112643 / 31250000)) * ((217903701 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13084) : ℝ)) (tA 13084 * 165 ^ 2 + 26 / (10 * 13084)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((217903701 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((112643 / 31250000)) ^ 2) * ((53293477 / 40000000000000000000000)) + ((402684477 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13084) : ℝ)) (√(26 / (10 * 13084) : ℝ)) d.D d.V d.P (√(tA 13084) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((112643 / 31250000)) * (((2087600063 / 1000000000000000)) * ((7300238147 / 200000000000000000))) + ((402684477 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13084) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((217903701 / 50000000000000000000) : ℝ) + ((402684477 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13084

namespace BstLean.Part266.Row13084
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13084 165 ∧
    0 ≤ (tableEnvelope C).f1 13084 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13084 165 ∧
    0 ≤ (tableEnvelope C).w1 13084 165 ∧ 0 ≤ (tableEnvelope C).w2 13084 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13084 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13084 165 ∧ 0 ≤ d.f1 13084 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13084 165 ∧ 0 ≤ d.w1 13084 165 ∧ 0 ≤ d.w2 13084 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13084 ≤ 2 * (228 / 100 : ℝ) / 13084 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13084 ≤ 2 * (370 / 100 : ℝ) / 13084 := by
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
    (completeRAData (tableEnvelope C) 13084 165).locationBound 13084 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13084 165).energyBound 13084 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13084 165) (d.f1 13084 165) d.f2 ≤
      32 * (((4253803757 / 1000000000000000000) : ℝ) + (177392631 / 125000000000000000) + (170545567 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13084 165) (d.w1 13084 165)
      (d.w2 13084 165) ≤
      32 * (((419118781 / 25000000000000000000) : ℝ) + (238556019 / 20000000000000000000) + (435811303 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13084 165) (d.f1 13084 165) d.f2 ≤
      ((4253803757 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4253803757 / 1000000000000000000)) * ((177392631 / 125000000000000000)) * (126 / 100) +
      2 * (((177392631 / 125000000000000000)) ^ 2 + 2 * ((4253803757 / 1000000000000000000)) * ((170545567 / 500000000000000000))) +
      6 * ((177392631 / 125000000000000000)) * ((170545567 / 500000000000000000)) * (126 / 100) + 8 * ((170545567 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13084 165) (d.f1 13084 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13084 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13084 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13084 165) (d.f1 13084 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13084 165) (d.w1 13084 165) (d.w2 13084 165)
  have hwexpr0 : 0 ≤ d.w0 13084 165 + d.w1 13084 165 * √(π / 2) +
      2 * d.w2 13084 165 + energyR16 13084 *
      radiusPolynomialRoot16 (d.w0 13084 165) (d.w1 13084 165) (d.w2 13084 165) := by
    positivity
  constructor
  · change (13084 : ℝ) ^ 8 * (mA 13084 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13084 165) (d.f1 13084 165) d.f2 + locationR16 13084 *
        radiusPolynomialRoot16 (d.f0 13084 165) (d.f1 13084 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13084 : ℝ) ^ 8 * (mA 13084 : ℝ) ^ 8 *
        ((((4253803757 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4253803757 / 1000000000000000000)) * ((177392631 / 125000000000000000)) * (126 / 100) +
          2 * (((177392631 / 125000000000000000)) ^ 2 + 2 * ((4253803757 / 1000000000000000000)) * ((170545567 / 500000000000000000))) +
          6 * ((177392631 / 125000000000000000)) * ((170545567 / 500000000000000000)) * (126 / 100) + 8 * ((170545567 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13084) *
          (32 * (((4253803757 / 1000000000000000000) : ℝ) + (177392631 / 125000000000000000) + (170545567 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13084 : ℝ) ^ 16 *
      (d.w0 13084 165 + d.w1 13084 165 * √(π / 2) + 2 * d.w2 13084 165 +
        energyR16 13084 * radiusPolynomialRoot16 (d.w0 13084 165) (d.w1 13084 165)
          (d.w2 13084 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13084 : ℝ) ^ 16 *
        (((419118781 / 25000000000000000000) : ℝ) + ((238556019 / 20000000000000000000)) * (126 / 100) + 2 * ((435811303 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13084) *
          (32 * (((419118781 / 25000000000000000000) : ℝ) + (238556019 / 20000000000000000000) + (435811303 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13084

/-! A coarse bound on the actual paper statistics constant at dimension 13085. -/
namespace BstLean.Part266.Row13085
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13083 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13083 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13083 128 ≤ (13337 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13337 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13085) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13085 : ℕ))
    (by norm_num : (13085 : ℕ) ≤ 16384)
  have ht : paperTail256 13085 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13085 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13085 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13085 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13085 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13085 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13083 128 * √(2 / (13085 : ℝ)) *
      (√(13085 : ℝ) + paperT0 13085 + paperTail256 13085) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13085 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13085 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13085 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13083 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13083 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13085 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13085

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13085
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13085 (61 / 100) 165 (17 / (100 * 13085)) (26 / (10 * 13085)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13085 (61 / 100) 165 (17 / (100 * 13085)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (435707487 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1331929669 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4024360331 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13085 / 13085 * (61 / 100)) ^ 4 * inverseRadius8 (13085 - 1) /
            envelopeGap 13085 (61 / 100) 165 (17 / (100 * 13085)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13085

namespace BstLean.Part266.Row13085
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13085 165 ≤ (2126495957 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13085 165 ≤ (1418870113 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (34102599 / 100000000000000000)
  w0 : (tableEnvelope C).w0 13085 165 ≤ (1676090947 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13085 165 ≤ (596253359 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13085 165 ≤ (217855693 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (435707487 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (435707487 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1331929669 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4024360331 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1802219 / 500000000) : ℝ) ≤ √(17 / (100 * 13085) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13085) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2087360743 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36495611641 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13085) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13085) ≤ (108078989 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13085) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13085 * (165 : ℝ) ^ 2 + 26 / (10 * 13085) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13085) : ℝ)) (tA 13085 * 165 ^ 2 + 26 / (10 * 13085)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1802219 / 500000000))) * ((435707487 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1802219 / 500000000)) ^ 3) * ((1331929669 / 1000000000000000000000000))) + ((4024360331 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1802219 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13085) : ℝ)) d.D d.V d.P (√(tA 13085) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1802219 / 500000000)) ^ 2 * (((2087360743 / 1000000000000000)) * ((36495611641 / 1000000000000000000)))) + ((4024360331 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13085) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1802219 / 500000000)) * ((435707487 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13085) : ℝ)) (tA 13085 * 165 ^ 2 + 26 / (10 * 13085)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((435707487 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1802219 / 500000000)) ^ 2) * ((1331929669 / 1000000000000000000000000)) + ((4024360331 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13085) : ℝ)) (√(26 / (10 * 13085) : ℝ)) d.D d.V d.P (√(tA 13085) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1802219 / 500000000)) * (((2087360743 / 1000000000000000)) * ((36495611641 / 1000000000000000000))) + ((4024360331 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13085) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((435707487 / 100000000000000000000) : ℝ) + ((4024360331 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13085

namespace BstLean.Part266.Row13085
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13085 165 ∧
    0 ≤ (tableEnvelope C).f1 13085 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13085 165 ∧
    0 ≤ (tableEnvelope C).w1 13085 165 ∧ 0 ≤ (tableEnvelope C).w2 13085 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13085 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13085 165 ∧ 0 ≤ d.f1 13085 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13085 165 ∧ 0 ≤ d.w1 13085 165 ∧ 0 ≤ d.w2 13085 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13085 ≤ 2 * (228 / 100 : ℝ) / 13085 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13085 ≤ 2 * (370 / 100 : ℝ) / 13085 := by
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
    (completeRAData (tableEnvelope C) 13085 165).locationBound 13085 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13085 165).energyBound 13085 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13085 165) (d.f1 13085 165) d.f2 ≤
      32 * (((2126495957 / 500000000000000000) : ℝ) + (1418870113 / 1000000000000000000) + (34102599 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13085 165) (d.w1 13085 165)
      (d.w2 13085 165) ≤
      32 * (((1676090947 / 100000000000000000000) : ℝ) + (596253359 / 50000000000000000000) + (217855693 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13085 165) (d.f1 13085 165) d.f2 ≤
      ((2126495957 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2126495957 / 500000000000000000)) * ((1418870113 / 1000000000000000000)) * (126 / 100) +
      2 * (((1418870113 / 1000000000000000000)) ^ 2 + 2 * ((2126495957 / 500000000000000000)) * ((34102599 / 100000000000000000))) +
      6 * ((1418870113 / 1000000000000000000)) * ((34102599 / 100000000000000000)) * (126 / 100) + 8 * ((34102599 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13085 165) (d.f1 13085 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13085 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13085 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13085 165) (d.f1 13085 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13085 165) (d.w1 13085 165) (d.w2 13085 165)
  have hwexpr0 : 0 ≤ d.w0 13085 165 + d.w1 13085 165 * √(π / 2) +
      2 * d.w2 13085 165 + energyR16 13085 *
      radiusPolynomialRoot16 (d.w0 13085 165) (d.w1 13085 165) (d.w2 13085 165) := by
    positivity
  constructor
  · change (13085 : ℝ) ^ 8 * (mA 13085 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13085 165) (d.f1 13085 165) d.f2 + locationR16 13085 *
        radiusPolynomialRoot16 (d.f0 13085 165) (d.f1 13085 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13085 : ℝ) ^ 8 * (mA 13085 : ℝ) ^ 8 *
        ((((2126495957 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2126495957 / 500000000000000000)) * ((1418870113 / 1000000000000000000)) * (126 / 100) +
          2 * (((1418870113 / 1000000000000000000)) ^ 2 + 2 * ((2126495957 / 500000000000000000)) * ((34102599 / 100000000000000000))) +
          6 * ((1418870113 / 1000000000000000000)) * ((34102599 / 100000000000000000)) * (126 / 100) + 8 * ((34102599 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13085) *
          (32 * (((2126495957 / 500000000000000000) : ℝ) + (1418870113 / 1000000000000000000) + (34102599 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13085 : ℝ) ^ 16 *
      (d.w0 13085 165 + d.w1 13085 165 * √(π / 2) + 2 * d.w2 13085 165 +
        energyR16 13085 * radiusPolynomialRoot16 (d.w0 13085 165) (d.w1 13085 165)
          (d.w2 13085 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13085 : ℝ) ^ 16 *
        (((1676090947 / 100000000000000000000) : ℝ) + ((596253359 / 50000000000000000000)) * (126 / 100) + 2 * ((217855693 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13085) *
          (32 * (((1676090947 / 100000000000000000000) : ℝ) + (596253359 / 50000000000000000000) + (217855693 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13085

/-! A coarse bound on the actual paper statistics constant at dimension 13086. -/
namespace BstLean.Part266.Row13086
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13084 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13084 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13084 128 ≤ (13338 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13338 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13086) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13086 : ℕ))
    (by norm_num : (13086 : ℕ) ≤ 16384)
  have ht : paperTail256 13086 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13086 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13086 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13086 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13086 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13086 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13084 128 * √(2 / (13086 : ℝ)) *
      (√(13086 : ℝ) + paperT0 13086 + paperTail256 13086) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13086 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13086 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13086 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13084 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13084 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13086 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13086

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13086
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13086 (61 / 100) 165 (17 / (100 * 13086)) (26 / (10 * 13086)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13086 (61 / 100) 165 (17 / (100 * 13086)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (435607603 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1331522569 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (2010938809 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13086 / 13086 * (61 / 100)) ^ 4 * inverseRadius8 (13086 - 1) /
            envelopeGap 13086 (61 / 100) 165 (17 / (100 * 13086)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13086

namespace BstLean.Part266.Row13086
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13086 165 ≤ (531522543 / 125000000000000000)
  f1 : (tableEnvelope C).f1 13086 165 ≤ (44331227 / 31250000000000000)
  f2 : (tableEnvelope C).f2 ≤ (170480433 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13086 165 ≤ (837853449 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13086 165 ≤ (149029179 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 13086 165 ≤ (435611499 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (435607603 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (435607603 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1331522569 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (2010938809 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((36043 / 10000000) : ℝ) ≤ √(17 / (100 * 13086) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13086) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (208712147 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4561254229 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13086) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13086) ≤ (10807073 / 100000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13086) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13086 * (165 : ℝ) ^ 2 + 26 / (10 * 13086) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13086) : ℝ)) (tA 13086 * 165 ^ 2 + 26 / (10 * 13086)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((36043 / 10000000))) * ((435607603 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((36043 / 10000000)) ^ 3) * ((1331522569 / 1000000000000000000000000))) + ((2010938809 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((36043 / 10000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13086) : ℝ)) d.D d.V d.P (√(tA 13086) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((36043 / 10000000)) ^ 2 * (((208712147 / 100000000000000)) * ((4561254229 / 125000000000000000)))) + ((2010938809 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13086) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((36043 / 10000000)) * ((435607603 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13086) : ℝ)) (tA 13086 * 165 ^ 2 + 26 / (10 * 13086)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((435607603 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((36043 / 10000000)) ^ 2) * ((1331522569 / 1000000000000000000000000)) + ((2010938809 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13086) : ℝ)) (√(26 / (10 * 13086) : ℝ)) d.D d.V d.P (√(tA 13086) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((36043 / 10000000)) * (((208712147 / 100000000000000)) * ((4561254229 / 125000000000000000))) + ((2010938809 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13086) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((435607603 / 100000000000000000000) : ℝ) + ((2010938809 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13086

namespace BstLean.Part266.Row13086
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13086 165 ∧
    0 ≤ (tableEnvelope C).f1 13086 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13086 165 ∧
    0 ≤ (tableEnvelope C).w1 13086 165 ∧ 0 ≤ (tableEnvelope C).w2 13086 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13086 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13086 165 ∧ 0 ≤ d.f1 13086 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13086 165 ∧ 0 ≤ d.w1 13086 165 ∧ 0 ≤ d.w2 13086 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13086 ≤ 2 * (228 / 100 : ℝ) / 13086 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13086 ≤ 2 * (370 / 100 : ℝ) / 13086 := by
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
    (completeRAData (tableEnvelope C) 13086 165).locationBound 13086 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13086 165).energyBound 13086 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13086 165) (d.f1 13086 165) d.f2 ≤
      32 * (((531522543 / 125000000000000000) : ℝ) + (44331227 / 31250000000000000) + (170480433 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13086 165) (d.w1 13086 165)
      (d.w2 13086 165) ≤
      32 * (((837853449 / 50000000000000000000) : ℝ) + (149029179 / 12500000000000000000) + (435611499 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13086 165) (d.f1 13086 165) d.f2 ≤
      ((531522543 / 125000000000000000) : ℝ) ^ 2 + 2 * ((531522543 / 125000000000000000)) * ((44331227 / 31250000000000000)) * (126 / 100) +
      2 * (((44331227 / 31250000000000000)) ^ 2 + 2 * ((531522543 / 125000000000000000)) * ((170480433 / 500000000000000000))) +
      6 * ((44331227 / 31250000000000000)) * ((170480433 / 500000000000000000)) * (126 / 100) + 8 * ((170480433 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13086 165) (d.f1 13086 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13086 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13086 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13086 165) (d.f1 13086 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13086 165) (d.w1 13086 165) (d.w2 13086 165)
  have hwexpr0 : 0 ≤ d.w0 13086 165 + d.w1 13086 165 * √(π / 2) +
      2 * d.w2 13086 165 + energyR16 13086 *
      radiusPolynomialRoot16 (d.w0 13086 165) (d.w1 13086 165) (d.w2 13086 165) := by
    positivity
  constructor
  · change (13086 : ℝ) ^ 8 * (mA 13086 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13086 165) (d.f1 13086 165) d.f2 + locationR16 13086 *
        radiusPolynomialRoot16 (d.f0 13086 165) (d.f1 13086 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13086 : ℝ) ^ 8 * (mA 13086 : ℝ) ^ 8 *
        ((((531522543 / 125000000000000000) : ℝ) ^ 2 + 2 * ((531522543 / 125000000000000000)) * ((44331227 / 31250000000000000)) * (126 / 100) +
          2 * (((44331227 / 31250000000000000)) ^ 2 + 2 * ((531522543 / 125000000000000000)) * ((170480433 / 500000000000000000))) +
          6 * ((44331227 / 31250000000000000)) * ((170480433 / 500000000000000000)) * (126 / 100) + 8 * ((170480433 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13086) *
          (32 * (((531522543 / 125000000000000000) : ℝ) + (44331227 / 31250000000000000) + (170480433 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13086 : ℝ) ^ 16 *
      (d.w0 13086 165 + d.w1 13086 165 * √(π / 2) + 2 * d.w2 13086 165 +
        energyR16 13086 * radiusPolynomialRoot16 (d.w0 13086 165) (d.w1 13086 165)
          (d.w2 13086 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13086 : ℝ) ^ 16 *
        (((837853449 / 50000000000000000000) : ℝ) + ((149029179 / 12500000000000000000)) * (126 / 100) + 2 * ((435611499 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13086) *
          (32 * (((837853449 / 50000000000000000000) : ℝ) + (149029179 / 12500000000000000000) + (435611499 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13086

/-! A coarse bound on the actual paper statistics constant at dimension 13087. -/
namespace BstLean.Part266.Row13087
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13085 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13085 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13085 128 ≤ (13339 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13339 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13087) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13087 : ℕ))
    (by norm_num : (13087 : ℕ) ≤ 16384)
  have ht : paperTail256 13087 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13087 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13087 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13087 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13087 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13087 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13085 128 * √(2 / (13087 : ℝ)) *
      (√(13087 : ℝ) + paperT0 13087 + paperTail256 13087) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13087 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13087 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13087 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13085 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13085 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13087 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13087

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13087
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13087 (61 / 100) 165 (17 / (100 * 13087)) (26 / (10 * 13087)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13087 (61 / 100) 165 (17 / (100 * 13087)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (435507749 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (166389453 / 125000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4019396629 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13087 / 13087 * (61 / 100)) ^ 4 * inverseRadius8 (13087 - 1) /
            envelopeGap 13087 (61 / 100) 165 (17 / (100 * 13087)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13087

namespace BstLean.Part266.Row13087
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13087 165 ≤ (4251369043 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13087 165 ≤ (709164249 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (4261197 / 12500000000000000)
  w0 : (tableEnvelope C).w0 13087 165 ≤ (1675322977 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13087 165 ≤ (1191960233 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13087 165 ≤ (435511643 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (435507749 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (435507749 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (166389453 / 125000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4019396629 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1802081 / 500000000) : ℝ) ≤ √(17 / (100 * 13087) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13087) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1043441121 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18242228647 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13087) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13087) ≤ (13507809 / 125000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13087) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13087 * (165 : ℝ) ^ 2 + 26 / (10 * 13087) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13087) : ℝ)) (tA 13087 * 165 ^ 2 + 26 / (10 * 13087)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1802081 / 500000000))) * ((435507749 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1802081 / 500000000)) ^ 3) * ((166389453 / 125000000000000000000000))) + ((4019396629 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1802081 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13087) : ℝ)) d.D d.V d.P (√(tA 13087) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1802081 / 500000000)) ^ 2 * (((1043441121 / 500000000000000)) * ((18242228647 / 500000000000000000)))) + ((4019396629 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13087) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1802081 / 500000000)) * ((435507749 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13087) : ℝ)) (tA 13087 * 165 ^ 2 + 26 / (10 * 13087)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((435507749 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1802081 / 500000000)) ^ 2) * ((166389453 / 125000000000000000000000)) + ((4019396629 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13087) : ℝ)) (√(26 / (10 * 13087) : ℝ)) d.D d.V d.P (√(tA 13087) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1802081 / 500000000)) * (((1043441121 / 500000000000000)) * ((18242228647 / 500000000000000000))) + ((4019396629 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13087) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((435507749 / 100000000000000000000) : ℝ) + ((4019396629 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13087

namespace BstLean.Part266.Row13087
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13087 165 ∧
    0 ≤ (tableEnvelope C).f1 13087 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13087 165 ∧
    0 ≤ (tableEnvelope C).w1 13087 165 ∧ 0 ≤ (tableEnvelope C).w2 13087 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13087 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13087 165 ∧ 0 ≤ d.f1 13087 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13087 165 ∧ 0 ≤ d.w1 13087 165 ∧ 0 ≤ d.w2 13087 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13087 ≤ 2 * (228 / 100 : ℝ) / 13087 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13087 ≤ 2 * (370 / 100 : ℝ) / 13087 := by
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
    (completeRAData (tableEnvelope C) 13087 165).locationBound 13087 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13087 165).energyBound 13087 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13087 165) (d.f1 13087 165) d.f2 ≤
      32 * (((4251369043 / 1000000000000000000) : ℝ) + (709164249 / 500000000000000000) + (4261197 / 12500000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13087 165) (d.w1 13087 165)
      (d.w2 13087 165) ≤
      32 * (((1675322977 / 100000000000000000000) : ℝ) + (1191960233 / 100000000000000000000) + (435511643 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13087 165) (d.f1 13087 165) d.f2 ≤
      ((4251369043 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4251369043 / 1000000000000000000)) * ((709164249 / 500000000000000000)) * (126 / 100) +
      2 * (((709164249 / 500000000000000000)) ^ 2 + 2 * ((4251369043 / 1000000000000000000)) * ((4261197 / 12500000000000000))) +
      6 * ((709164249 / 500000000000000000)) * ((4261197 / 12500000000000000)) * (126 / 100) + 8 * ((4261197 / 12500000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13087 165) (d.f1 13087 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13087 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13087 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13087 165) (d.f1 13087 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13087 165) (d.w1 13087 165) (d.w2 13087 165)
  have hwexpr0 : 0 ≤ d.w0 13087 165 + d.w1 13087 165 * √(π / 2) +
      2 * d.w2 13087 165 + energyR16 13087 *
      radiusPolynomialRoot16 (d.w0 13087 165) (d.w1 13087 165) (d.w2 13087 165) := by
    positivity
  constructor
  · change (13087 : ℝ) ^ 8 * (mA 13087 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13087 165) (d.f1 13087 165) d.f2 + locationR16 13087 *
        radiusPolynomialRoot16 (d.f0 13087 165) (d.f1 13087 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13087 : ℝ) ^ 8 * (mA 13087 : ℝ) ^ 8 *
        ((((4251369043 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4251369043 / 1000000000000000000)) * ((709164249 / 500000000000000000)) * (126 / 100) +
          2 * (((709164249 / 500000000000000000)) ^ 2 + 2 * ((4251369043 / 1000000000000000000)) * ((4261197 / 12500000000000000))) +
          6 * ((709164249 / 500000000000000000)) * ((4261197 / 12500000000000000)) * (126 / 100) + 8 * ((4261197 / 12500000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13087) *
          (32 * (((4251369043 / 1000000000000000000) : ℝ) + (709164249 / 500000000000000000) + (4261197 / 12500000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13087 : ℝ) ^ 16 *
      (d.w0 13087 165 + d.w1 13087 165 * √(π / 2) + 2 * d.w2 13087 165 +
        energyR16 13087 * radiusPolynomialRoot16 (d.w0 13087 165) (d.w1 13087 165)
          (d.w2 13087 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13087 : ℝ) ^ 16 *
        (((1675322977 / 100000000000000000000) : ℝ) + ((1191960233 / 100000000000000000000)) * (126 / 100) + 2 * ((435511643 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13087) *
          (32 * (((1675322977 / 100000000000000000000) : ℝ) + (1191960233 / 100000000000000000000) + (435511643 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13087

/-! A coarse bound on the actual paper statistics constant at dimension 13088. -/
namespace BstLean.Part266.Row13088
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13086 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13086 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13086 128 ≤ (13340 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13340 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13088) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13088 : ℕ))
    (by norm_num : (13088 : ℕ) ≤ 16384)
  have ht : paperTail256 13088 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13088 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13088 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13088 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13088 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13088 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13086 128 * √(2 / (13088 : ℝ)) *
      (√(13088 : ℝ) + paperT0 13088 + paperTail256 13088) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13088 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13088 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13088 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13086 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13086 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13088 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13088

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13088
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13088 (61 / 100) 165 (17 / (100 * 13088)) (26 / (10 * 13088)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13088 (61 / 100) 165 (17 / (100 * 13088)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (17416317 / 4000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (266141767 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1004229341 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13088 / 13088 * (61 / 100)) ^ 4 * inverseRadius8 (13088 - 1) /
            envelopeGap 13088 (61 / 100) 165 (17 / (100 * 13088)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13088

namespace BstLean.Part266.Row13088
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13088 165 ≤ (4250554609 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13088 165 ≤ (141805703 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (340830577 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13088 165 ≤ (1674938497 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13088 165 ≤ (148960849 / 12500000000000000000)
  w2 : (tableEnvelope C).w2 13088 165 ≤ (435411817 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (17416317 / 4000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (17416317 / 4000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (266141767 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1004229341 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((144161 / 40000000) : ℝ) ≤ √(17 / (100 * 13088) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13088) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1043321529 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18239441021 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13088) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13088) ≤ (21610843 / 200000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13088) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13088 * (165 : ℝ) ^ 2 + 26 / (10 * 13088) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13088) : ℝ)) (tA 13088 * 165 ^ 2 + 26 / (10 * 13088)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((144161 / 40000000))) * ((17416317 / 4000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((144161 / 40000000)) ^ 3) * ((266141767 / 200000000000000000000000))) + ((1004229341 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((144161 / 40000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13088) : ℝ)) d.D d.V d.P (√(tA 13088) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((144161 / 40000000)) ^ 2 * (((1043321529 / 500000000000000)) * ((18239441021 / 500000000000000000)))) + ((1004229341 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13088) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((144161 / 40000000)) * ((17416317 / 4000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13088) : ℝ)) (tA 13088 * 165 ^ 2 + 26 / (10 * 13088)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((17416317 / 4000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((144161 / 40000000)) ^ 2) * ((266141767 / 200000000000000000000000)) + ((1004229341 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13088) : ℝ)) (√(26 / (10 * 13088) : ℝ)) d.D d.V d.P (√(tA 13088) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((144161 / 40000000)) * (((1043321529 / 500000000000000)) * ((18239441021 / 500000000000000000))) + ((1004229341 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13088) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((17416317 / 4000000000000000000) : ℝ) + ((1004229341 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13088

namespace BstLean.Part266.Row13088
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13088 165 ∧
    0 ≤ (tableEnvelope C).f1 13088 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13088 165 ∧
    0 ≤ (tableEnvelope C).w1 13088 165 ∧ 0 ≤ (tableEnvelope C).w2 13088 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13088 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13088 165 ∧ 0 ≤ d.f1 13088 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13088 165 ∧ 0 ≤ d.w1 13088 165 ∧ 0 ≤ d.w2 13088 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13088 ≤ 2 * (228 / 100 : ℝ) / 13088 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13088 ≤ 2 * (370 / 100 : ℝ) / 13088 := by
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
    (completeRAData (tableEnvelope C) 13088 165).locationBound 13088 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13088 165).energyBound 13088 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13088 165) (d.f1 13088 165) d.f2 ≤
      32 * (((4250554609 / 1000000000000000000) : ℝ) + (141805703 / 100000000000000000) + (340830577 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13088 165) (d.w1 13088 165)
      (d.w2 13088 165) ≤
      32 * (((1674938497 / 100000000000000000000) : ℝ) + (148960849 / 12500000000000000000) + (435411817 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13088 165) (d.f1 13088 165) d.f2 ≤
      ((4250554609 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4250554609 / 1000000000000000000)) * ((141805703 / 100000000000000000)) * (126 / 100) +
      2 * (((141805703 / 100000000000000000)) ^ 2 + 2 * ((4250554609 / 1000000000000000000)) * ((340830577 / 1000000000000000000))) +
      6 * ((141805703 / 100000000000000000)) * ((340830577 / 1000000000000000000)) * (126 / 100) + 8 * ((340830577 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13088 165) (d.f1 13088 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13088 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13088 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13088 165) (d.f1 13088 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13088 165) (d.w1 13088 165) (d.w2 13088 165)
  have hwexpr0 : 0 ≤ d.w0 13088 165 + d.w1 13088 165 * √(π / 2) +
      2 * d.w2 13088 165 + energyR16 13088 *
      radiusPolynomialRoot16 (d.w0 13088 165) (d.w1 13088 165) (d.w2 13088 165) := by
    positivity
  constructor
  · change (13088 : ℝ) ^ 8 * (mA 13088 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13088 165) (d.f1 13088 165) d.f2 + locationR16 13088 *
        radiusPolynomialRoot16 (d.f0 13088 165) (d.f1 13088 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13088 : ℝ) ^ 8 * (mA 13088 : ℝ) ^ 8 *
        ((((4250554609 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4250554609 / 1000000000000000000)) * ((141805703 / 100000000000000000)) * (126 / 100) +
          2 * (((141805703 / 100000000000000000)) ^ 2 + 2 * ((4250554609 / 1000000000000000000)) * ((340830577 / 1000000000000000000))) +
          6 * ((141805703 / 100000000000000000)) * ((340830577 / 1000000000000000000)) * (126 / 100) + 8 * ((340830577 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13088) *
          (32 * (((4250554609 / 1000000000000000000) : ℝ) + (141805703 / 100000000000000000) + (340830577 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13088 : ℝ) ^ 16 *
      (d.w0 13088 165 + d.w1 13088 165 * √(π / 2) + 2 * d.w2 13088 165 +
        energyR16 13088 * radiusPolynomialRoot16 (d.w0 13088 165) (d.w1 13088 165)
          (d.w2 13088 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13088 : ℝ) ^ 16 *
        (((1674938497 / 100000000000000000000) : ℝ) + ((148960849 / 12500000000000000000)) * (126 / 100) + 2 * ((435411817 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13088) *
          (32 * (((1674938497 / 100000000000000000000) : ℝ) + (148960849 / 12500000000000000000) + (435411817 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13088

/-! A coarse bound on the actual paper statistics constant at dimension 13089. -/
namespace BstLean.Part266.Row13089
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13087 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13087 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13087 128 ≤ (13341 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13341 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13089) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13089 : ℕ))
    (by norm_num : (13089 : ℕ) ≤ 16384)
  have ht : paperTail256 13089 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13089 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13089 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13089 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13089 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13089 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13087 128 * √(2 / (13089 : ℝ)) *
      (√(13089 : ℝ) + paperT0 13089 + paperTail256 13089) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13089 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13089 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13089 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13087 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13087 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13089 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13089

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13089
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13089 (61 / 100) 165 (17 / (100 * 13089)) (26 / (10 * 13089)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13089 (61 / 100) 165 (17 / (100 * 13089)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (108827033 / 25000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (665151101 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4014439821 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13089 / 13089 * (61 / 100)) ^ 4 * inverseRadius8 (13089 - 1) /
            envelopeGap 13089 (61 / 100) 165 (17 / (100 * 13089)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13089

namespace BstLean.Part266.Row13089
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13089 165 ≤ (4249743853 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13089 165 ≤ (283557287 / 200000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (340765509 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13089 165 ≤ (1674554833 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13089 165 ≤ (1191413771 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13089 165 ≤ (435312021 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (108827033 / 25000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (108827033 / 25000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (665151101 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4014439821 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3603887 / 1000000000) : ℝ) ≤ √(17 / (100 * 13089) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13089) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2086403921 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (9118327019 / 250000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13089) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13089) ≤ (2701149 / 25000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13089) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13089 * (165 : ℝ) ^ 2 + 26 / (10 * 13089) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13089) : ℝ)) (tA 13089 * 165 ^ 2 + 26 / (10 * 13089)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3603887 / 1000000000))) * ((108827033 / 25000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3603887 / 1000000000)) ^ 3) * ((665151101 / 500000000000000000000000))) + ((4014439821 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3603887 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13089) : ℝ)) d.D d.V d.P (√(tA 13089) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3603887 / 1000000000)) ^ 2 * (((2086403921 / 1000000000000000)) * ((9118327019 / 250000000000000000)))) + ((4014439821 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13089) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3603887 / 1000000000)) * ((108827033 / 25000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13089) : ℝ)) (tA 13089 * 165 ^ 2 + 26 / (10 * 13089)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((108827033 / 25000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3603887 / 1000000000)) ^ 2) * ((665151101 / 500000000000000000000000)) + ((4014439821 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13089) : ℝ)) (√(26 / (10 * 13089) : ℝ)) d.D d.V d.P (√(tA 13089) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3603887 / 1000000000)) * (((2086403921 / 1000000000000000)) * ((9118327019 / 250000000000000000))) + ((4014439821 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13089) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((108827033 / 25000000000000000000) : ℝ) + ((4014439821 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13089

namespace BstLean.Part266.Row13089
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13089 165 ∧
    0 ≤ (tableEnvelope C).f1 13089 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13089 165 ∧
    0 ≤ (tableEnvelope C).w1 13089 165 ∧ 0 ≤ (tableEnvelope C).w2 13089 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13089 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13089 165 ∧ 0 ≤ d.f1 13089 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13089 165 ∧ 0 ≤ d.w1 13089 165 ∧ 0 ≤ d.w2 13089 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13089 ≤ 2 * (228 / 100 : ℝ) / 13089 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13089 ≤ 2 * (370 / 100 : ℝ) / 13089 := by
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
    (completeRAData (tableEnvelope C) 13089 165).locationBound 13089 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13089 165).energyBound 13089 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13089 165) (d.f1 13089 165) d.f2 ≤
      32 * (((4249743853 / 1000000000000000000) : ℝ) + (283557287 / 200000000000000000) + (340765509 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13089 165) (d.w1 13089 165)
      (d.w2 13089 165) ≤
      32 * (((1674554833 / 100000000000000000000) : ℝ) + (1191413771 / 100000000000000000000) + (435312021 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13089 165) (d.f1 13089 165) d.f2 ≤
      ((4249743853 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4249743853 / 1000000000000000000)) * ((283557287 / 200000000000000000)) * (126 / 100) +
      2 * (((283557287 / 200000000000000000)) ^ 2 + 2 * ((4249743853 / 1000000000000000000)) * ((340765509 / 1000000000000000000))) +
      6 * ((283557287 / 200000000000000000)) * ((340765509 / 1000000000000000000)) * (126 / 100) + 8 * ((340765509 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13089 165) (d.f1 13089 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13089 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13089 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13089 165) (d.f1 13089 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13089 165) (d.w1 13089 165) (d.w2 13089 165)
  have hwexpr0 : 0 ≤ d.w0 13089 165 + d.w1 13089 165 * √(π / 2) +
      2 * d.w2 13089 165 + energyR16 13089 *
      radiusPolynomialRoot16 (d.w0 13089 165) (d.w1 13089 165) (d.w2 13089 165) := by
    positivity
  constructor
  · change (13089 : ℝ) ^ 8 * (mA 13089 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13089 165) (d.f1 13089 165) d.f2 + locationR16 13089 *
        radiusPolynomialRoot16 (d.f0 13089 165) (d.f1 13089 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13089 : ℝ) ^ 8 * (mA 13089 : ℝ) ^ 8 *
        ((((4249743853 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4249743853 / 1000000000000000000)) * ((283557287 / 200000000000000000)) * (126 / 100) +
          2 * (((283557287 / 200000000000000000)) ^ 2 + 2 * ((4249743853 / 1000000000000000000)) * ((340765509 / 1000000000000000000))) +
          6 * ((283557287 / 200000000000000000)) * ((340765509 / 1000000000000000000)) * (126 / 100) + 8 * ((340765509 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13089) *
          (32 * (((4249743853 / 1000000000000000000) : ℝ) + (283557287 / 200000000000000000) + (340765509 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13089 : ℝ) ^ 16 *
      (d.w0 13089 165 + d.w1 13089 165 * √(π / 2) + 2 * d.w2 13089 165 +
        energyR16 13089 * radiusPolynomialRoot16 (d.w0 13089 165) (d.w1 13089 165)
          (d.w2 13089 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13089 : ℝ) ^ 16 *
        (((1674554833 / 100000000000000000000) : ℝ) + ((1191413771 / 100000000000000000000)) * (126 / 100) + 2 * ((435312021 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13089) *
          (32 * (((1674554833 / 100000000000000000000) : ℝ) + (1191413771 / 100000000000000000000) + (435312021 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13089

/-! A coarse bound on the actual paper statistics constant at dimension 13090. -/
namespace BstLean.Part266.Row13090
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13088 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13088 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13088 128 ≤ (13342 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13342 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13090) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13090 : ℕ))
    (by norm_num : (13090 : ℕ) ≤ 16384)
  have ht : paperTail256 13090 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13090 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13090 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13090 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13090 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13090 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13088 128 * √(2 / (13090 : ℝ)) *
      (√(13090 : ℝ) + paperT0 13090 + paperTail256 13090) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13090 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13090 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13090 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13088 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13088 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13090 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13090

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13090
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13090 (61 / 100) 165 (17 / (100 * 13090)) (26 / (10 * 13090)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13090 (61 / 100) 165 (17 / (100 * 13090)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (43520837 / 10000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1329895723 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4011963999 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13090 / 13090 * (61 / 100)) ^ 4 * inverseRadius8 (13090 - 1) /
            envelopeGap 13090 (61 / 100) 165 (17 / (100 * 13090)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13090

namespace BstLean.Part266.Row13090
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13090 165 ≤ (1062233341 / 250000000000000000)
  f1 : (tableEnvelope C).f1 13090 165 ≤ (354378981 / 250000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (17035023 / 50000000000000000)
  w0 : (tableEnvelope C).w0 13090 165 ≤ (1674171297 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13090 165 ≤ (29778521 / 2500000000000000000)
  w2 : (tableEnvelope C).w2 13090 165 ≤ (435212257 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (43520837 / 10000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (43520837 / 10000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1329895723 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4011963999 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3603749 / 1000000000) : ℝ) ≤ √(17 / (100 * 13090) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13090) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2086164831 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (3646773537 / 100000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13090) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13090) ≤ (54018853 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13090) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13090 * (165 : ℝ) ^ 2 + 26 / (10 * 13090) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13090) : ℝ)) (tA 13090 * 165 ^ 2 + 26 / (10 * 13090)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3603749 / 1000000000))) * ((43520837 / 10000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3603749 / 1000000000)) ^ 3) * ((1329895723 / 1000000000000000000000000))) + ((4011963999 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3603749 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13090) : ℝ)) d.D d.V d.P (√(tA 13090) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3603749 / 1000000000)) ^ 2 * (((2086164831 / 1000000000000000)) * ((3646773537 / 100000000000000000)))) + ((4011963999 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13090) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3603749 / 1000000000)) * ((43520837 / 10000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13090) : ℝ)) (tA 13090 * 165 ^ 2 + 26 / (10 * 13090)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((43520837 / 10000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3603749 / 1000000000)) ^ 2) * ((1329895723 / 1000000000000000000000000)) + ((4011963999 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13090) : ℝ)) (√(26 / (10 * 13090) : ℝ)) d.D d.V d.P (√(tA 13090) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3603749 / 1000000000)) * (((2086164831 / 1000000000000000)) * ((3646773537 / 100000000000000000))) + ((4011963999 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13090) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((43520837 / 10000000000000000000) : ℝ) + ((4011963999 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13090

namespace BstLean.Part266.Row13090
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13090 165 ∧
    0 ≤ (tableEnvelope C).f1 13090 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13090 165 ∧
    0 ≤ (tableEnvelope C).w1 13090 165 ∧ 0 ≤ (tableEnvelope C).w2 13090 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13090 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13090 165 ∧ 0 ≤ d.f1 13090 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13090 165 ∧ 0 ≤ d.w1 13090 165 ∧ 0 ≤ d.w2 13090 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13090 ≤ 2 * (228 / 100 : ℝ) / 13090 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13090 ≤ 2 * (370 / 100 : ℝ) / 13090 := by
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
    (completeRAData (tableEnvelope C) 13090 165).locationBound 13090 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13090 165).energyBound 13090 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13090 165) (d.f1 13090 165) d.f2 ≤
      32 * (((1062233341 / 250000000000000000) : ℝ) + (354378981 / 250000000000000000) + (17035023 / 50000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13090 165) (d.w1 13090 165)
      (d.w2 13090 165) ≤
      32 * (((1674171297 / 100000000000000000000) : ℝ) + (29778521 / 2500000000000000000) + (435212257 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13090 165) (d.f1 13090 165) d.f2 ≤
      ((1062233341 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1062233341 / 250000000000000000)) * ((354378981 / 250000000000000000)) * (126 / 100) +
      2 * (((354378981 / 250000000000000000)) ^ 2 + 2 * ((1062233341 / 250000000000000000)) * ((17035023 / 50000000000000000))) +
      6 * ((354378981 / 250000000000000000)) * ((17035023 / 50000000000000000)) * (126 / 100) + 8 * ((17035023 / 50000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13090 165) (d.f1 13090 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13090 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13090 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13090 165) (d.f1 13090 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13090 165) (d.w1 13090 165) (d.w2 13090 165)
  have hwexpr0 : 0 ≤ d.w0 13090 165 + d.w1 13090 165 * √(π / 2) +
      2 * d.w2 13090 165 + energyR16 13090 *
      radiusPolynomialRoot16 (d.w0 13090 165) (d.w1 13090 165) (d.w2 13090 165) := by
    positivity
  constructor
  · change (13090 : ℝ) ^ 8 * (mA 13090 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13090 165) (d.f1 13090 165) d.f2 + locationR16 13090 *
        radiusPolynomialRoot16 (d.f0 13090 165) (d.f1 13090 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13090 : ℝ) ^ 8 * (mA 13090 : ℝ) ^ 8 *
        ((((1062233341 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1062233341 / 250000000000000000)) * ((354378981 / 250000000000000000)) * (126 / 100) +
          2 * (((354378981 / 250000000000000000)) ^ 2 + 2 * ((1062233341 / 250000000000000000)) * ((17035023 / 50000000000000000))) +
          6 * ((354378981 / 250000000000000000)) * ((17035023 / 50000000000000000)) * (126 / 100) + 8 * ((17035023 / 50000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13090) *
          (32 * (((1062233341 / 250000000000000000) : ℝ) + (354378981 / 250000000000000000) + (17035023 / 50000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13090 : ℝ) ^ 16 *
      (d.w0 13090 165 + d.w1 13090 165 * √(π / 2) + 2 * d.w2 13090 165 +
        energyR16 13090 * radiusPolynomialRoot16 (d.w0 13090 165) (d.w1 13090 165)
          (d.w2 13090 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13090 : ℝ) ^ 16 *
        (((1674171297 / 100000000000000000000) : ℝ) + ((29778521 / 2500000000000000000)) * (126 / 100) + 2 * ((435212257 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13090) *
          (32 * (((1674171297 / 100000000000000000000) : ℝ) + (29778521 / 2500000000000000000) + (435212257 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13090

/-! A coarse bound on the actual paper statistics constant at dimension 13091. -/
namespace BstLean.Part266.Row13091
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13089 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13089 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13089 128 ≤ (13343 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13343 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13091) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13091 : ℕ))
    (by norm_num : (13091 : ℕ) ≤ 16384)
  have ht : paperTail256 13091 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13091 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13091 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13091 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13091 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13091 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13089 128 * √(2 / (13091 : ℝ)) *
      (√(13091 : ℝ) + paperT0 13091 + paperTail256 13091) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13091 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13091 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13091 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13089 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13089 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13091 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13091

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13091
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13091 (61 / 100) 165 (17 / (100 * 13091)) (26 / (10 * 13091)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13091 (61 / 100) 165 (17 / (100 * 13091)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (217554319 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (6647447 / 5000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (501186237 / 125000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13091 / 13091 * (61 / 100)) ^ 4 * inverseRadius8 (13091 - 1) /
            envelopeGap 13091 (61 / 100) 165 (17 / (100 * 13091)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13091

namespace BstLean.Part266.Row13091
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13091 165 ≤ (66376871 / 15625000000000000)
  f1 : (tableEnvelope C).f1 13091 165 ≤ (177155589 / 125000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (68127067 / 200000000000000000)
  w0 : (tableEnvelope C).w0 13091 165 ≤ (836893601 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13091 165 ≤ (238173533 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 13091 165 ≤ (217556261 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (217554319 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (217554319 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (6647447 / 5000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (501186237 / 125000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((900903 / 250000000) : ℝ) ≤ √(17 / (100 * 13091) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13091) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (417185157 / 200000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (2278885247 / 62500000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13091) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13091) ≤ (108029453 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13091) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13091 * (165 : ℝ) ^ 2 + 26 / (10 * 13091) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13091) : ℝ)) (tA 13091 * 165 ^ 2 + 26 / (10 * 13091)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((900903 / 250000000))) * ((217554319 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((900903 / 250000000)) ^ 3) * ((6647447 / 5000000000000000000000))) + ((501186237 / 125000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((900903 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13091) : ℝ)) d.D d.V d.P (√(tA 13091) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((900903 / 250000000)) ^ 2 * (((417185157 / 200000000000000)) * ((2278885247 / 62500000000000000)))) + ((501186237 / 125000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13091) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((900903 / 250000000)) * ((217554319 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13091) : ℝ)) (tA 13091 * 165 ^ 2 + 26 / (10 * 13091)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((217554319 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((900903 / 250000000)) ^ 2) * ((6647447 / 5000000000000000000000)) + ((501186237 / 125000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13091) : ℝ)) (√(26 / (10 * 13091) : ℝ)) d.D d.V d.P (√(tA 13091) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((900903 / 250000000)) * (((417185157 / 200000000000000)) * ((2278885247 / 62500000000000000))) + ((501186237 / 125000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13091) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((217554319 / 50000000000000000000) : ℝ) + ((501186237 / 125000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13091

namespace BstLean.Part266.Row13091
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13091 165 ∧
    0 ≤ (tableEnvelope C).f1 13091 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13091 165 ∧
    0 ≤ (tableEnvelope C).w1 13091 165 ∧ 0 ≤ (tableEnvelope C).w2 13091 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13091 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13091 165 ∧ 0 ≤ d.f1 13091 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13091 165 ∧ 0 ≤ d.w1 13091 165 ∧ 0 ≤ d.w2 13091 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13091 ≤ 2 * (228 / 100 : ℝ) / 13091 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13091 ≤ 2 * (370 / 100 : ℝ) / 13091 := by
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
    (completeRAData (tableEnvelope C) 13091 165).locationBound 13091 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13091 165).energyBound 13091 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13091 165) (d.f1 13091 165) d.f2 ≤
      32 * (((66376871 / 15625000000000000) : ℝ) + (177155589 / 125000000000000000) + (68127067 / 200000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13091 165) (d.w1 13091 165)
      (d.w2 13091 165) ≤
      32 * (((836893601 / 50000000000000000000) : ℝ) + (238173533 / 20000000000000000000) + (217556261 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13091 165) (d.f1 13091 165) d.f2 ≤
      ((66376871 / 15625000000000000) : ℝ) ^ 2 + 2 * ((66376871 / 15625000000000000)) * ((177155589 / 125000000000000000)) * (126 / 100) +
      2 * (((177155589 / 125000000000000000)) ^ 2 + 2 * ((66376871 / 15625000000000000)) * ((68127067 / 200000000000000000))) +
      6 * ((177155589 / 125000000000000000)) * ((68127067 / 200000000000000000)) * (126 / 100) + 8 * ((68127067 / 200000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13091 165) (d.f1 13091 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13091 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13091 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13091 165) (d.f1 13091 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13091 165) (d.w1 13091 165) (d.w2 13091 165)
  have hwexpr0 : 0 ≤ d.w0 13091 165 + d.w1 13091 165 * √(π / 2) +
      2 * d.w2 13091 165 + energyR16 13091 *
      radiusPolynomialRoot16 (d.w0 13091 165) (d.w1 13091 165) (d.w2 13091 165) := by
    positivity
  constructor
  · change (13091 : ℝ) ^ 8 * (mA 13091 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13091 165) (d.f1 13091 165) d.f2 + locationR16 13091 *
        radiusPolynomialRoot16 (d.f0 13091 165) (d.f1 13091 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13091 : ℝ) ^ 8 * (mA 13091 : ℝ) ^ 8 *
        ((((66376871 / 15625000000000000) : ℝ) ^ 2 + 2 * ((66376871 / 15625000000000000)) * ((177155589 / 125000000000000000)) * (126 / 100) +
          2 * (((177155589 / 125000000000000000)) ^ 2 + 2 * ((66376871 / 15625000000000000)) * ((68127067 / 200000000000000000))) +
          6 * ((177155589 / 125000000000000000)) * ((68127067 / 200000000000000000)) * (126 / 100) + 8 * ((68127067 / 200000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13091) *
          (32 * (((66376871 / 15625000000000000) : ℝ) + (177155589 / 125000000000000000) + (68127067 / 200000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13091 : ℝ) ^ 16 *
      (d.w0 13091 165 + d.w1 13091 165 * √(π / 2) + 2 * d.w2 13091 165 +
        energyR16 13091 * radiusPolynomialRoot16 (d.w0 13091 165) (d.w1 13091 165)
          (d.w2 13091 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13091 : ℝ) ^ 16 *
        (((836893601 / 50000000000000000000) : ℝ) + ((238173533 / 20000000000000000000)) * (126 / 100) + 2 * ((217556261 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13091) *
          (32 * (((836893601 / 50000000000000000000) : ℝ) + (238173533 / 20000000000000000000) + (217556261 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13091

/-! A coarse bound on the actual paper statistics constant at dimension 13092. -/
namespace BstLean.Part266.Row13092
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13090 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13090 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13090 128 ≤ (13344 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13344 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13092) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13092 : ℕ))
    (by norm_num : (13092 : ℕ) ≤ 16384)
  have ht : paperTail256 13092 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13092 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13092 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13092 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13092 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13092 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13090 128 * √(2 / (13092 : ℝ)) *
      (√(13092 : ℝ) + paperT0 13092 + paperTail256 13092) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13092 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13092 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13092 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13090 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13090 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13092 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13092

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13092
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13092 (61 / 100) 165 (17 / (100 * 13092)) (26 / (10 * 13092)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13092 (61 / 100) 165 (17 / (100 * 13092)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (54376117 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (41533851 / 31250000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4007017511 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13092 / 13092 * (61 / 100)) ^ 4 * inverseRadius8 (13092 - 1) /
            envelopeGap 13092 (61 / 100) 165 (17 / (100 * 13092)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13092

namespace BstLean.Part266.Row13092
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13092 165 ≤ (4247309797 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13092 165 ≤ (141697437 / 100000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (340570323 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13092 165 ≤ (836701961 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13092 165 ≤ (1190594909 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13092 165 ≤ (217506409 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (54376117 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (54376117 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (41533851 / 31250000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4007017511 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1801737 / 500000000) : ℝ) ≤ √(17 / (100 * 13092) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13092) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (4073607 / 1953125000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36456593807 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13092) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13092) ≤ (108021201 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13092) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13092 * (165 : ℝ) ^ 2 + 26 / (10 * 13092) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13092) : ℝ)) (tA 13092 * 165 ^ 2 + 26 / (10 * 13092)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1801737 / 500000000))) * ((54376117 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1801737 / 500000000)) ^ 3) * ((41533851 / 31250000000000000000000))) + ((4007017511 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1801737 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13092) : ℝ)) d.D d.V d.P (√(tA 13092) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1801737 / 500000000)) ^ 2 * (((4073607 / 1953125000000)) * ((36456593807 / 1000000000000000000)))) + ((4007017511 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13092) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1801737 / 500000000)) * ((54376117 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13092) : ℝ)) (tA 13092 * 165 ^ 2 + 26 / (10 * 13092)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((54376117 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1801737 / 500000000)) ^ 2) * ((41533851 / 31250000000000000000000)) + ((4007017511 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13092) : ℝ)) (√(26 / (10 * 13092) : ℝ)) d.D d.V d.P (√(tA 13092) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1801737 / 500000000)) * (((4073607 / 1953125000000)) * ((36456593807 / 1000000000000000000))) + ((4007017511 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13092) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((54376117 / 12500000000000000000) : ℝ) + ((4007017511 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13092

namespace BstLean.Part266.Row13092
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13092 165 ∧
    0 ≤ (tableEnvelope C).f1 13092 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13092 165 ∧
    0 ≤ (tableEnvelope C).w1 13092 165 ∧ 0 ≤ (tableEnvelope C).w2 13092 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13092 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13092 165 ∧ 0 ≤ d.f1 13092 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13092 165 ∧ 0 ≤ d.w1 13092 165 ∧ 0 ≤ d.w2 13092 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13092 ≤ 2 * (228 / 100 : ℝ) / 13092 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13092 ≤ 2 * (370 / 100 : ℝ) / 13092 := by
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
    (completeRAData (tableEnvelope C) 13092 165).locationBound 13092 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13092 165).energyBound 13092 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13092 165) (d.f1 13092 165) d.f2 ≤
      32 * (((4247309797 / 1000000000000000000) : ℝ) + (141697437 / 100000000000000000) + (340570323 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13092 165) (d.w1 13092 165)
      (d.w2 13092 165) ≤
      32 * (((836701961 / 50000000000000000000) : ℝ) + (1190594909 / 100000000000000000000) + (217506409 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13092 165) (d.f1 13092 165) d.f2 ≤
      ((4247309797 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4247309797 / 1000000000000000000)) * ((141697437 / 100000000000000000)) * (126 / 100) +
      2 * (((141697437 / 100000000000000000)) ^ 2 + 2 * ((4247309797 / 1000000000000000000)) * ((340570323 / 1000000000000000000))) +
      6 * ((141697437 / 100000000000000000)) * ((340570323 / 1000000000000000000)) * (126 / 100) + 8 * ((340570323 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13092 165) (d.f1 13092 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13092 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13092 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13092 165) (d.f1 13092 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13092 165) (d.w1 13092 165) (d.w2 13092 165)
  have hwexpr0 : 0 ≤ d.w0 13092 165 + d.w1 13092 165 * √(π / 2) +
      2 * d.w2 13092 165 + energyR16 13092 *
      radiusPolynomialRoot16 (d.w0 13092 165) (d.w1 13092 165) (d.w2 13092 165) := by
    positivity
  constructor
  · change (13092 : ℝ) ^ 8 * (mA 13092 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13092 165) (d.f1 13092 165) d.f2 + locationR16 13092 *
        radiusPolynomialRoot16 (d.f0 13092 165) (d.f1 13092 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13092 : ℝ) ^ 8 * (mA 13092 : ℝ) ^ 8 *
        ((((4247309797 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4247309797 / 1000000000000000000)) * ((141697437 / 100000000000000000)) * (126 / 100) +
          2 * (((141697437 / 100000000000000000)) ^ 2 + 2 * ((4247309797 / 1000000000000000000)) * ((340570323 / 1000000000000000000))) +
          6 * ((141697437 / 100000000000000000)) * ((340570323 / 1000000000000000000)) * (126 / 100) + 8 * ((340570323 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13092) *
          (32 * (((4247309797 / 1000000000000000000) : ℝ) + (141697437 / 100000000000000000) + (340570323 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13092 : ℝ) ^ 16 *
      (d.w0 13092 165 + d.w1 13092 165 * √(π / 2) + 2 * d.w2 13092 165 +
        energyR16 13092 * radiusPolynomialRoot16 (d.w0 13092 165) (d.w1 13092 165)
          (d.w2 13092 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13092 : ℝ) ^ 16 *
        (((836701961 / 50000000000000000000) : ℝ) + ((1190594909 / 100000000000000000000)) * (126 / 100) + 2 * ((217506409 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13092) *
          (32 * (((836701961 / 50000000000000000000) : ℝ) + (1190594909 / 100000000000000000000) + (217506409 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13092

/-! A coarse bound on the actual paper statistics constant at dimension 13093. -/
namespace BstLean.Part266.Row13093
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13091 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13091 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13091 128 ≤ (13345 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13345 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13093) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13093 : ℕ))
    (by norm_num : (13093 : ℕ) ≤ 16384)
  have ht : paperTail256 13093 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13093 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13093 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13093 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13093 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13093 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13091 128 * √(2 / (13093 : ℝ)) *
      (√(13093 : ℝ) + paperT0 13093 + paperTail256 13093) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13093 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13093 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13093 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13091 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13091 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13093 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13093

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13093
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13093 (61 / 100) 165 (17 / (100 * 13093)) (26 / (10 * 13093)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13093 (61 / 100) 165 (17 / (100 * 13093)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (86981853 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1328677219 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (4004546843 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13093 / 13093 * (61 / 100)) ^ 4 * inverseRadius8 (13093 - 1) /
            envelopeGap 13093 (61 / 100) 165 (17 / (100 * 13093)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13093

namespace BstLean.Part266.Row13093
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13093 165 ≤ (4246500121 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13093 165 ≤ (1416704113 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (34050533 / 100000000000000000)
  w0 : (tableEnvelope C).w0 13093 165 ≤ (167302077 / 10000000000000000000)
  w1 : (tableEnvelope C).w1 13093 165 ≤ (1190322243 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13093 165 ≤ (86982629 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (86981853 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (86981853 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1328677219 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (4004546843 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((450417 / 125000000) : ℝ) ≤ √(17 / (100 * 13093) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13093) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (208544783 / 100000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18225512469 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13093) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13093) ≤ (108012951 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13093) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13093 * (165 : ℝ) ^ 2 + 26 / (10 * 13093) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13093) : ℝ)) (tA 13093 * 165 ^ 2 + 26 / (10 * 13093)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((450417 / 125000000))) * ((86981853 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((450417 / 125000000)) ^ 3) * ((1328677219 / 1000000000000000000000000))) + ((4004546843 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((450417 / 125000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13093) : ℝ)) d.D d.V d.P (√(tA 13093) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((450417 / 125000000)) ^ 2 * (((208544783 / 100000000000000)) * ((18225512469 / 500000000000000000)))) + ((4004546843 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13093) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((450417 / 125000000)) * ((86981853 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13093) : ℝ)) (tA 13093 * 165 ^ 2 + 26 / (10 * 13093)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((86981853 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((450417 / 125000000)) ^ 2) * ((1328677219 / 1000000000000000000000000)) + ((4004546843 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13093) : ℝ)) (√(26 / (10 * 13093) : ℝ)) d.D d.V d.P (√(tA 13093) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((450417 / 125000000)) * (((208544783 / 100000000000000)) * ((18225512469 / 500000000000000000))) + ((4004546843 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13093) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((86981853 / 20000000000000000000) : ℝ) + ((4004546843 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13093

namespace BstLean.Part266.Row13093
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13093 165 ∧
    0 ≤ (tableEnvelope C).f1 13093 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13093 165 ∧
    0 ≤ (tableEnvelope C).w1 13093 165 ∧ 0 ≤ (tableEnvelope C).w2 13093 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13093 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13093 165 ∧ 0 ≤ d.f1 13093 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13093 165 ∧ 0 ≤ d.w1 13093 165 ∧ 0 ≤ d.w2 13093 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13093 ≤ 2 * (228 / 100 : ℝ) / 13093 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13093 ≤ 2 * (370 / 100 : ℝ) / 13093 := by
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
    (completeRAData (tableEnvelope C) 13093 165).locationBound 13093 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13093 165).energyBound 13093 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13093 165) (d.f1 13093 165) d.f2 ≤
      32 * (((4246500121 / 1000000000000000000) : ℝ) + (1416704113 / 1000000000000000000) + (34050533 / 100000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13093 165) (d.w1 13093 165)
      (d.w2 13093 165) ≤
      32 * (((167302077 / 10000000000000000000) : ℝ) + (1190322243 / 100000000000000000000) + (86982629 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13093 165) (d.f1 13093 165) d.f2 ≤
      ((4246500121 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4246500121 / 1000000000000000000)) * ((1416704113 / 1000000000000000000)) * (126 / 100) +
      2 * (((1416704113 / 1000000000000000000)) ^ 2 + 2 * ((4246500121 / 1000000000000000000)) * ((34050533 / 100000000000000000))) +
      6 * ((1416704113 / 1000000000000000000)) * ((34050533 / 100000000000000000)) * (126 / 100) + 8 * ((34050533 / 100000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13093 165) (d.f1 13093 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13093 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13093 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13093 165) (d.f1 13093 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13093 165) (d.w1 13093 165) (d.w2 13093 165)
  have hwexpr0 : 0 ≤ d.w0 13093 165 + d.w1 13093 165 * √(π / 2) +
      2 * d.w2 13093 165 + energyR16 13093 *
      radiusPolynomialRoot16 (d.w0 13093 165) (d.w1 13093 165) (d.w2 13093 165) := by
    positivity
  constructor
  · change (13093 : ℝ) ^ 8 * (mA 13093 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13093 165) (d.f1 13093 165) d.f2 + locationR16 13093 *
        radiusPolynomialRoot16 (d.f0 13093 165) (d.f1 13093 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13093 : ℝ) ^ 8 * (mA 13093 : ℝ) ^ 8 *
        ((((4246500121 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4246500121 / 1000000000000000000)) * ((1416704113 / 1000000000000000000)) * (126 / 100) +
          2 * (((1416704113 / 1000000000000000000)) ^ 2 + 2 * ((4246500121 / 1000000000000000000)) * ((34050533 / 100000000000000000))) +
          6 * ((1416704113 / 1000000000000000000)) * ((34050533 / 100000000000000000)) * (126 / 100) + 8 * ((34050533 / 100000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13093) *
          (32 * (((4246500121 / 1000000000000000000) : ℝ) + (1416704113 / 1000000000000000000) + (34050533 / 100000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13093 : ℝ) ^ 16 *
      (d.w0 13093 165 + d.w1 13093 165 * √(π / 2) + 2 * d.w2 13093 165 +
        energyR16 13093 * radiusPolynomialRoot16 (d.w0 13093 165) (d.w1 13093 165)
          (d.w2 13093 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13093 : ℝ) ^ 16 *
        (((167302077 / 10000000000000000000) : ℝ) + ((1190322243 / 100000000000000000000)) * (126 / 100) + 2 * ((86982629 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13093) *
          (32 * (((167302077 / 10000000000000000000) : ℝ) + (1190322243 / 100000000000000000000) + (86982629 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13093

/-! A coarse bound on the actual paper statistics constant at dimension 13094. -/
namespace BstLean.Part266.Row13094
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13092 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13092 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13092 128 ≤ (13346 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13346 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13094) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13094 : ℕ))
    (by norm_num : (13094 : ℕ) ≤ 16384)
  have ht : paperTail256 13094 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13094 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13094 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13094 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13094 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13094 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13092 128 * √(2 / (13094 : ℝ)) *
      (√(13094 : ℝ) + paperT0 13094 + paperTail256 13094) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13094 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13094 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13094 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13092 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13092 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13094 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13094

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13094
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13094 (61 / 100) 165 (17 / (100 * 13094)) (26 / (10 * 13094)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13094 (61 / 100) 165 (17 / (100 * 13094)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (54351203 / 12500000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1328271361 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (400207789 / 100000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13094 / 13094 * (61 / 100)) ^ 4 * inverseRadius8 (13094 - 1) /
            envelopeGap 13094 (61 / 100) 165 (17 / (100 * 13094)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13094

namespace BstLean.Part266.Row13094
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13094 165 ≤ (265355457 / 62500000000000000)
  f1 : (tableEnvelope C).f1 13094 165 ≤ (708216577 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (170220131 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13094 165 ≤ (836318529 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13094 165 ≤ (595024667 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13094 165 ≤ (434813501 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (54351203 / 12500000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (54351203 / 12500000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1328271361 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (400207789 / 100000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3603199 / 1000000000) : ℝ) ≤ √(17 / (100 * 13094) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13094) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (52130223 / 25000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (569460271 / 15625000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13094) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13094) ≤ (54002351 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13094) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13094 * (165 : ℝ) ^ 2 + 26 / (10 * 13094) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13094) : ℝ)) (tA 13094 * 165 ^ 2 + 26 / (10 * 13094)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3603199 / 1000000000))) * ((54351203 / 12500000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3603199 / 1000000000)) ^ 3) * ((1328271361 / 1000000000000000000000000))) + ((400207789 / 100000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3603199 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13094) : ℝ)) d.D d.V d.P (√(tA 13094) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3603199 / 1000000000)) ^ 2 * (((52130223 / 25000000000000)) * ((569460271 / 15625000000000000)))) + ((400207789 / 100000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13094) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3603199 / 1000000000)) * ((54351203 / 12500000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13094) : ℝ)) (tA 13094 * 165 ^ 2 + 26 / (10 * 13094)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((54351203 / 12500000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3603199 / 1000000000)) ^ 2) * ((1328271361 / 1000000000000000000000000)) + ((400207789 / 100000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13094) : ℝ)) (√(26 / (10 * 13094) : ℝ)) d.D d.V d.P (√(tA 13094) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3603199 / 1000000000)) * (((52130223 / 25000000000000)) * ((569460271 / 15625000000000000))) + ((400207789 / 100000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13094) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((54351203 / 12500000000000000000) : ℝ) + ((400207789 / 100000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13094

namespace BstLean.Part266.Row13094
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13094 165 ∧
    0 ≤ (tableEnvelope C).f1 13094 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13094 165 ∧
    0 ≤ (tableEnvelope C).w1 13094 165 ∧ 0 ≤ (tableEnvelope C).w2 13094 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13094 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13094 165 ∧ 0 ≤ d.f1 13094 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13094 165 ∧ 0 ≤ d.w1 13094 165 ∧ 0 ≤ d.w2 13094 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13094 ≤ 2 * (228 / 100 : ℝ) / 13094 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13094 ≤ 2 * (370 / 100 : ℝ) / 13094 := by
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
    (completeRAData (tableEnvelope C) 13094 165).locationBound 13094 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13094 165).energyBound 13094 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13094 165) (d.f1 13094 165) d.f2 ≤
      32 * (((265355457 / 62500000000000000) : ℝ) + (708216577 / 500000000000000000) + (170220131 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13094 165) (d.w1 13094 165)
      (d.w2 13094 165) ≤
      32 * (((836318529 / 50000000000000000000) : ℝ) + (595024667 / 50000000000000000000) + (434813501 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13094 165) (d.f1 13094 165) d.f2 ≤
      ((265355457 / 62500000000000000) : ℝ) ^ 2 + 2 * ((265355457 / 62500000000000000)) * ((708216577 / 500000000000000000)) * (126 / 100) +
      2 * (((708216577 / 500000000000000000)) ^ 2 + 2 * ((265355457 / 62500000000000000)) * ((170220131 / 500000000000000000))) +
      6 * ((708216577 / 500000000000000000)) * ((170220131 / 500000000000000000)) * (126 / 100) + 8 * ((170220131 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13094 165) (d.f1 13094 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13094 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13094 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13094 165) (d.f1 13094 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13094 165) (d.w1 13094 165) (d.w2 13094 165)
  have hwexpr0 : 0 ≤ d.w0 13094 165 + d.w1 13094 165 * √(π / 2) +
      2 * d.w2 13094 165 + energyR16 13094 *
      radiusPolynomialRoot16 (d.w0 13094 165) (d.w1 13094 165) (d.w2 13094 165) := by
    positivity
  constructor
  · change (13094 : ℝ) ^ 8 * (mA 13094 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13094 165) (d.f1 13094 165) d.f2 + locationR16 13094 *
        radiusPolynomialRoot16 (d.f0 13094 165) (d.f1 13094 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13094 : ℝ) ^ 8 * (mA 13094 : ℝ) ^ 8 *
        ((((265355457 / 62500000000000000) : ℝ) ^ 2 + 2 * ((265355457 / 62500000000000000)) * ((708216577 / 500000000000000000)) * (126 / 100) +
          2 * (((708216577 / 500000000000000000)) ^ 2 + 2 * ((265355457 / 62500000000000000)) * ((170220131 / 500000000000000000))) +
          6 * ((708216577 / 500000000000000000)) * ((170220131 / 500000000000000000)) * (126 / 100) + 8 * ((170220131 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13094) *
          (32 * (((265355457 / 62500000000000000) : ℝ) + (708216577 / 500000000000000000) + (170220131 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13094 : ℝ) ^ 16 *
      (d.w0 13094 165 + d.w1 13094 165 * √(π / 2) + 2 * d.w2 13094 165 +
        energyR16 13094 * radiusPolynomialRoot16 (d.w0 13094 165) (d.w1 13094 165)
          (d.w2 13094 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13094 : ℝ) ^ 16 *
        (((836318529 / 50000000000000000000) : ℝ) + ((595024667 / 50000000000000000000)) * (126 / 100) + 2 * ((434813501 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13094) *
          (32 * (((836318529 / 50000000000000000000) : ℝ) + (595024667 / 50000000000000000000) + (434813501 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13094

/-! A coarse bound on the actual paper statistics constant at dimension 13095. -/
namespace BstLean.Part266.Row13095
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13093 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13093 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13093 128 ≤ (13347 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13347 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13095) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13095 : ℕ))
    (by norm_num : (13095 : ℕ) ≤ 16384)
  have ht : paperTail256 13095 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13095 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13095 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13095 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13095 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13095 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13093 128 * √(2 / (13095 : ℝ)) *
      (√(13095 : ℝ) + paperT0 13095 + paperTail256 13095) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13095 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13095 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13095 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13093 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13093 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13095 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13095

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13095
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13095 (61 / 100) 165 (17 / (100 * 13095)) (26 / (10 * 13095)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13095 (61 / 100) 165 (17 / (100 * 13095)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (217355007 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (663932829 / 500000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (999902663 / 250000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13095 / 13095 * (61 / 100)) ^ 4 * inverseRadius8 (13095 - 1) /
            envelopeGap 13095 (61 / 100) 165 (17 / (100 * 13095)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13095

namespace BstLean.Part266.Row13095
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13095 165 ≤ (132652443 / 31250000000000000)
  f1 : (tableEnvelope C).f1 13095 165 ≤ (1416163067 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (340375307 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13095 165 ≤ (836127081 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13095 165 ≤ (237955369 / 20000000000000000000)
  w2 : (tableEnvelope C).w2 13095 165 ≤ (434713889 / 100000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (217355007 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (217355007 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (663932829 / 500000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (999902663 / 250000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3603061 / 1000000000) : ℝ) ≤ √(17 / (100 * 13095) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13095) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1042485029 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (36439891027 / 1000000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13095) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13095) ≤ (53998227 / 500000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13095) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13095 * (165 : ℝ) ^ 2 + 26 / (10 * 13095) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13095) : ℝ)) (tA 13095 * 165 ^ 2 + 26 / (10 * 13095)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3603061 / 1000000000))) * ((217355007 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3603061 / 1000000000)) ^ 3) * ((663932829 / 500000000000000000000000))) + ((999902663 / 250000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3603061 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13095) : ℝ)) d.D d.V d.P (√(tA 13095) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3603061 / 1000000000)) ^ 2 * (((1042485029 / 500000000000000)) * ((36439891027 / 1000000000000000000)))) + ((999902663 / 250000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13095) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3603061 / 1000000000)) * ((217355007 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13095) : ℝ)) (tA 13095 * 165 ^ 2 + 26 / (10 * 13095)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((217355007 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3603061 / 1000000000)) ^ 2) * ((663932829 / 500000000000000000000000)) + ((999902663 / 250000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13095) : ℝ)) (√(26 / (10 * 13095) : ℝ)) d.D d.V d.P (√(tA 13095) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3603061 / 1000000000)) * (((1042485029 / 500000000000000)) * ((36439891027 / 1000000000000000000))) + ((999902663 / 250000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13095) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((217355007 / 50000000000000000000) : ℝ) + ((999902663 / 250000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13095

namespace BstLean.Part266.Row13095
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13095 165 ∧
    0 ≤ (tableEnvelope C).f1 13095 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13095 165 ∧
    0 ≤ (tableEnvelope C).w1 13095 165 ∧ 0 ≤ (tableEnvelope C).w2 13095 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13095 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13095 165 ∧ 0 ≤ d.f1 13095 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13095 165 ∧ 0 ≤ d.w1 13095 165 ∧ 0 ≤ d.w2 13095 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13095 ≤ 2 * (228 / 100 : ℝ) / 13095 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13095 ≤ 2 * (370 / 100 : ℝ) / 13095 := by
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
    (completeRAData (tableEnvelope C) 13095 165).locationBound 13095 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13095 165).energyBound 13095 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13095 165) (d.f1 13095 165) d.f2 ≤
      32 * (((132652443 / 31250000000000000) : ℝ) + (1416163067 / 1000000000000000000) + (340375307 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13095 165) (d.w1 13095 165)
      (d.w2 13095 165) ≤
      32 * (((836127081 / 50000000000000000000) : ℝ) + (237955369 / 20000000000000000000) + (434713889 / 100000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13095 165) (d.f1 13095 165) d.f2 ≤
      ((132652443 / 31250000000000000) : ℝ) ^ 2 + 2 * ((132652443 / 31250000000000000)) * ((1416163067 / 1000000000000000000)) * (126 / 100) +
      2 * (((1416163067 / 1000000000000000000)) ^ 2 + 2 * ((132652443 / 31250000000000000)) * ((340375307 / 1000000000000000000))) +
      6 * ((1416163067 / 1000000000000000000)) * ((340375307 / 1000000000000000000)) * (126 / 100) + 8 * ((340375307 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13095 165) (d.f1 13095 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13095 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13095 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13095 165) (d.f1 13095 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13095 165) (d.w1 13095 165) (d.w2 13095 165)
  have hwexpr0 : 0 ≤ d.w0 13095 165 + d.w1 13095 165 * √(π / 2) +
      2 * d.w2 13095 165 + energyR16 13095 *
      radiusPolynomialRoot16 (d.w0 13095 165) (d.w1 13095 165) (d.w2 13095 165) := by
    positivity
  constructor
  · change (13095 : ℝ) ^ 8 * (mA 13095 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13095 165) (d.f1 13095 165) d.f2 + locationR16 13095 *
        radiusPolynomialRoot16 (d.f0 13095 165) (d.f1 13095 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13095 : ℝ) ^ 8 * (mA 13095 : ℝ) ^ 8 *
        ((((132652443 / 31250000000000000) : ℝ) ^ 2 + 2 * ((132652443 / 31250000000000000)) * ((1416163067 / 1000000000000000000)) * (126 / 100) +
          2 * (((1416163067 / 1000000000000000000)) ^ 2 + 2 * ((132652443 / 31250000000000000)) * ((340375307 / 1000000000000000000))) +
          6 * ((1416163067 / 1000000000000000000)) * ((340375307 / 1000000000000000000)) * (126 / 100) + 8 * ((340375307 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13095) *
          (32 * (((132652443 / 31250000000000000) : ℝ) + (1416163067 / 1000000000000000000) + (340375307 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13095 : ℝ) ^ 16 *
      (d.w0 13095 165 + d.w1 13095 165 * √(π / 2) + 2 * d.w2 13095 165 +
        energyR16 13095 * radiusPolynomialRoot16 (d.w0 13095 165) (d.w1 13095 165)
          (d.w2 13095 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13095 : ℝ) ^ 16 *
        (((836127081 / 50000000000000000000) : ℝ) + ((237955369 / 20000000000000000000)) * (126 / 100) + 2 * ((434713889 / 100000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13095) *
          (32 * (((836127081 / 50000000000000000000) : ℝ) + (237955369 / 20000000000000000000) + (434713889 / 100000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13095

/-! A coarse bound on the actual paper statistics constant at dimension 13096. -/
namespace BstLean.Part266.Row13096
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13094 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13094 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13094 128 ≤ (13348 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13348 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13096) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13096 : ℕ))
    (by norm_num : (13096 : ℕ) ≤ 16384)
  have ht : paperTail256 13096 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13096 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13096 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13096 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13096 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13096 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13094 128 * √(2 / (13096 : ℝ)) *
      (√(13096 : ℝ) + paperT0 13096 + paperTail256 13096) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13096 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13096 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13096 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13094 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13094 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13096 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13096

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13096
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13096 (61 / 100) 165 (17 / (100 * 13096)) (26 / (10 * 13096)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13096 (61 / 100) 165 (17 / (100 * 13096)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (217305217 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (132746011 / 100000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (1998572563 / 500000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13096 / 13096 * (61 / 100)) ^ 4 * inverseRadius8 (13096 - 1) /
            envelopeGap 13096 (61 / 100) 165 (17 / (100 * 13096)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13096

namespace BstLean.Part266.Row13096
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13096 165 ≤ (4244065909 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13096 165 ≤ (707946139 / 500000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (85077569 / 250000000000000000)
  w0 : (tableEnvelope C).w0 13096 165 ≤ (835935353 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13096 165 ≤ (1189504113 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13096 165 ≤ (217307153 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (217305217 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (217305217 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (132746011 / 100000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (1998572563 / 500000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((900731 / 250000000) : ℝ) ≤ √(17 / (100 * 13096) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13096) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (52118281 / 25000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18217162993 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13096) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13096) ≤ (6749263 / 62500000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13096) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13096 * (165 : ℝ) ^ 2 + 26 / (10 * 13096) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13096) : ℝ)) (tA 13096 * 165 ^ 2 + 26 / (10 * 13096)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((900731 / 250000000))) * ((217305217 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((900731 / 250000000)) ^ 3) * ((132746011 / 100000000000000000000000))) + ((1998572563 / 500000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((900731 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13096) : ℝ)) d.D d.V d.P (√(tA 13096) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((900731 / 250000000)) ^ 2 * (((52118281 / 25000000000000)) * ((18217162993 / 500000000000000000)))) + ((1998572563 / 500000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13096) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((900731 / 250000000)) * ((217305217 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13096) : ℝ)) (tA 13096 * 165 ^ 2 + 26 / (10 * 13096)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((217305217 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((900731 / 250000000)) ^ 2) * ((132746011 / 100000000000000000000000)) + ((1998572563 / 500000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13096) : ℝ)) (√(26 / (10 * 13096) : ℝ)) d.D d.V d.P (√(tA 13096) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((900731 / 250000000)) * (((52118281 / 25000000000000)) * ((18217162993 / 500000000000000000))) + ((1998572563 / 500000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13096) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((217305217 / 50000000000000000000) : ℝ) + ((1998572563 / 500000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13096

namespace BstLean.Part266.Row13096
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13096 165 ∧
    0 ≤ (tableEnvelope C).f1 13096 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13096 165 ∧
    0 ≤ (tableEnvelope C).w1 13096 165 ∧ 0 ≤ (tableEnvelope C).w2 13096 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13096 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13096 165 ∧ 0 ≤ d.f1 13096 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13096 165 ∧ 0 ≤ d.w1 13096 165 ∧ 0 ≤ d.w2 13096 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13096 ≤ 2 * (228 / 100 : ℝ) / 13096 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13096 ≤ 2 * (370 / 100 : ℝ) / 13096 := by
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
    (completeRAData (tableEnvelope C) 13096 165).locationBound 13096 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13096 165).energyBound 13096 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13096 165) (d.f1 13096 165) d.f2 ≤
      32 * (((4244065909 / 1000000000000000000) : ℝ) + (707946139 / 500000000000000000) + (85077569 / 250000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13096 165) (d.w1 13096 165)
      (d.w2 13096 165) ≤
      32 * (((835935353 / 50000000000000000000) : ℝ) + (1189504113 / 100000000000000000000) + (217307153 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13096 165) (d.f1 13096 165) d.f2 ≤
      ((4244065909 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4244065909 / 1000000000000000000)) * ((707946139 / 500000000000000000)) * (126 / 100) +
      2 * (((707946139 / 500000000000000000)) ^ 2 + 2 * ((4244065909 / 1000000000000000000)) * ((85077569 / 250000000000000000))) +
      6 * ((707946139 / 500000000000000000)) * ((85077569 / 250000000000000000)) * (126 / 100) + 8 * ((85077569 / 250000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13096 165) (d.f1 13096 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13096 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13096 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13096 165) (d.f1 13096 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13096 165) (d.w1 13096 165) (d.w2 13096 165)
  have hwexpr0 : 0 ≤ d.w0 13096 165 + d.w1 13096 165 * √(π / 2) +
      2 * d.w2 13096 165 + energyR16 13096 *
      radiusPolynomialRoot16 (d.w0 13096 165) (d.w1 13096 165) (d.w2 13096 165) := by
    positivity
  constructor
  · change (13096 : ℝ) ^ 8 * (mA 13096 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13096 165) (d.f1 13096 165) d.f2 + locationR16 13096 *
        radiusPolynomialRoot16 (d.f0 13096 165) (d.f1 13096 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13096 : ℝ) ^ 8 * (mA 13096 : ℝ) ^ 8 *
        ((((4244065909 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4244065909 / 1000000000000000000)) * ((707946139 / 500000000000000000)) * (126 / 100) +
          2 * (((707946139 / 500000000000000000)) ^ 2 + 2 * ((4244065909 / 1000000000000000000)) * ((85077569 / 250000000000000000))) +
          6 * ((707946139 / 500000000000000000)) * ((85077569 / 250000000000000000)) * (126 / 100) + 8 * ((85077569 / 250000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13096) *
          (32 * (((4244065909 / 1000000000000000000) : ℝ) + (707946139 / 500000000000000000) + (85077569 / 250000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13096 : ℝ) ^ 16 *
      (d.w0 13096 165 + d.w1 13096 165 * √(π / 2) + 2 * d.w2 13096 165 +
        energyR16 13096 * radiusPolynomialRoot16 (d.w0 13096 165) (d.w1 13096 165)
          (d.w2 13096 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13096 : ℝ) ^ 16 *
        (((835935353 / 50000000000000000000) : ℝ) + ((1189504113 / 100000000000000000000)) * (126 / 100) + 2 * ((217307153 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13096) *
          (32 * (((835935353 / 50000000000000000000) : ℝ) + (1189504113 / 100000000000000000000) + (217307153 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13096

/-! A coarse bound on the actual paper statistics constant at dimension 13097. -/
namespace BstLean.Part266.Row13097
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13095 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13095 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13095 128 ≤ (13349 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13349 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13097) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13097 : ℕ))
    (by norm_num : (13097 : ℕ) ≤ 16384)
  have ht : paperTail256 13097 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13097 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13097 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13097 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13097 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13097 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13095 128 * √(2 / (13097 : ℝ)) *
      (√(13097 : ℝ) + paperT0 13097 + paperTail256 13097) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13097 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13097 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13097 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13095 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13095 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13097 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13097

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13097
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13097 (61 / 100) 165 (17 / (100 * 13097)) (26 / (10 * 13097)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13097 (61 / 100) 165 (17 / (100 * 13097)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (86902177 / 20000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1327054717 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3994681311 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13097 / 13097 * (61 / 100)) ^ 4 * inverseRadius8 (13097 - 1) /
            envelopeGap 13097 (61 / 100) 165 (17 / (100 * 13097)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13097

namespace BstLean.Part266.Row13097
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13097 165 ≤ (2121628657 / 500000000000000000)
  f1 : (tableEnvelope C).f1 13097 165 ≤ (1415622361 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (340245359 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13097 165 ≤ (835744033 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13097 165 ≤ (1189231801 / 100000000000000000000)
  w2 : (tableEnvelope C).w2 13097 165 ≤ (86902951 / 20000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (86902177 / 20000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (86902177 / 20000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1327054717 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3994681311 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((1801393 / 500000000) : ℝ) ≤ √(17 / (100 * 13097) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13097) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (2084492469 / 1000000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (18214381111 / 500000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13097) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13097) ≤ (107979963 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13097) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13097 * (165 : ℝ) ^ 2 + 26 / (10 * 13097) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13097) : ℝ)) (tA 13097 * 165 ^ 2 + 26 / (10 * 13097)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((1801393 / 500000000))) * ((86902177 / 20000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((1801393 / 500000000)) ^ 3) * ((1327054717 / 1000000000000000000000000))) + ((3994681311 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((1801393 / 500000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13097) : ℝ)) d.D d.V d.P (√(tA 13097) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((1801393 / 500000000)) ^ 2 * (((2084492469 / 1000000000000000)) * ((18214381111 / 500000000000000000)))) + ((3994681311 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13097) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((1801393 / 500000000)) * ((86902177 / 20000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13097) : ℝ)) (tA 13097 * 165 ^ 2 + 26 / (10 * 13097)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((86902177 / 20000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((1801393 / 500000000)) ^ 2) * ((1327054717 / 1000000000000000000000000)) + ((3994681311 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13097) : ℝ)) (√(26 / (10 * 13097) : ℝ)) d.D d.V d.P (√(tA 13097) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((1801393 / 500000000)) * (((2084492469 / 1000000000000000)) * ((18214381111 / 500000000000000000))) + ((3994681311 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13097) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((86902177 / 20000000000000000000) : ℝ) + ((3994681311 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13097

namespace BstLean.Part266.Row13097
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13097 165 ∧
    0 ≤ (tableEnvelope C).f1 13097 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13097 165 ∧
    0 ≤ (tableEnvelope C).w1 13097 165 ∧ 0 ≤ (tableEnvelope C).w2 13097 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13097 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13097 165 ∧ 0 ≤ d.f1 13097 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13097 165 ∧ 0 ≤ d.w1 13097 165 ∧ 0 ≤ d.w2 13097 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13097 ≤ 2 * (228 / 100 : ℝ) / 13097 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13097 ≤ 2 * (370 / 100 : ℝ) / 13097 := by
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
    (completeRAData (tableEnvelope C) 13097 165).locationBound 13097 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13097 165).energyBound 13097 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13097 165) (d.f1 13097 165) d.f2 ≤
      32 * (((2121628657 / 500000000000000000) : ℝ) + (1415622361 / 1000000000000000000) + (340245359 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13097 165) (d.w1 13097 165)
      (d.w2 13097 165) ≤
      32 * (((835744033 / 50000000000000000000) : ℝ) + (1189231801 / 100000000000000000000) + (86902951 / 20000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13097 165) (d.f1 13097 165) d.f2 ≤
      ((2121628657 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2121628657 / 500000000000000000)) * ((1415622361 / 1000000000000000000)) * (126 / 100) +
      2 * (((1415622361 / 1000000000000000000)) ^ 2 + 2 * ((2121628657 / 500000000000000000)) * ((340245359 / 1000000000000000000))) +
      6 * ((1415622361 / 1000000000000000000)) * ((340245359 / 1000000000000000000)) * (126 / 100) + 8 * ((340245359 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13097 165) (d.f1 13097 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13097 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13097 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13097 165) (d.f1 13097 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13097 165) (d.w1 13097 165) (d.w2 13097 165)
  have hwexpr0 : 0 ≤ d.w0 13097 165 + d.w1 13097 165 * √(π / 2) +
      2 * d.w2 13097 165 + energyR16 13097 *
      radiusPolynomialRoot16 (d.w0 13097 165) (d.w1 13097 165) (d.w2 13097 165) := by
    positivity
  constructor
  · change (13097 : ℝ) ^ 8 * (mA 13097 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13097 165) (d.f1 13097 165) d.f2 + locationR16 13097 *
        radiusPolynomialRoot16 (d.f0 13097 165) (d.f1 13097 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13097 : ℝ) ^ 8 * (mA 13097 : ℝ) ^ 8 *
        ((((2121628657 / 500000000000000000) : ℝ) ^ 2 + 2 * ((2121628657 / 500000000000000000)) * ((1415622361 / 1000000000000000000)) * (126 / 100) +
          2 * (((1415622361 / 1000000000000000000)) ^ 2 + 2 * ((2121628657 / 500000000000000000)) * ((340245359 / 1000000000000000000))) +
          6 * ((1415622361 / 1000000000000000000)) * ((340245359 / 1000000000000000000)) * (126 / 100) + 8 * ((340245359 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13097) *
          (32 * (((2121628657 / 500000000000000000) : ℝ) + (1415622361 / 1000000000000000000) + (340245359 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13097 : ℝ) ^ 16 *
      (d.w0 13097 165 + d.w1 13097 165 * √(π / 2) + 2 * d.w2 13097 165 +
        energyR16 13097 * radiusPolynomialRoot16 (d.w0 13097 165) (d.w1 13097 165)
          (d.w2 13097 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13097 : ℝ) ^ 16 *
        (((835744033 / 50000000000000000000) : ℝ) + ((1189231801 / 100000000000000000000)) * (126 / 100) + 2 * ((86902951 / 20000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13097) *
          (32 * (((835744033 / 50000000000000000000) : ℝ) + (1189231801 / 100000000000000000000) + (86902951 / 20000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13097

/-! A coarse bound on the actual paper statistics constant at dimension 13098. -/
namespace BstLean.Part266.Row13098
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13096 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13096 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13096 128 ≤ (13350 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13350 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13098) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13098 : ℕ))
    (by norm_num : (13098 : ℕ) ≤ 16384)
  have ht : paperTail256 13098 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13098 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13098 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13098 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13098 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13098 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13096 128 * √(2 / (13098 : ℝ)) *
      (√(13098 : ℝ) + paperT0 13098 + paperTail256 13098) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13098 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13098 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13098 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13096 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13096 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13098 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13098

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13098
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13098 (61 / 100) 165 (17 / (100 * 13098)) (26 / (10 * 13098)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13098 (61 / 100) 165 (17 / (100 * 13098)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (217205683 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (1326649479 / 1000000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3992219207 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13098 / 13098 * (61 / 100)) ^ 4 * inverseRadius8 (13098 - 1) /
            envelopeGap 13098 (61 / 100) 165 (17 / (100 * 13098)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13098

namespace BstLean.Part266.Row13098
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13098 165 ≤ (424244559 / 100000000000000000)
  f1 : (tableEnvelope C).f1 13098 165 ≤ (1415351741 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (170090183 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13098 165 ≤ (1671104867 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13098 165 ≤ (594479623 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13098 165 ≤ (217207617 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (217205683 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (217205683 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (1326649479 / 1000000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3992219207 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3602649 / 1000000000) : ℝ) ≤ √(17 / (100 * 13098) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13098) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (1042126871 / 500000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (4552899967 / 125000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13098) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13098) ≤ (107971719 / 1000000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13098) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13098 * (165 : ℝ) ^ 2 + 26 / (10 * 13098) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13098) : ℝ)) (tA 13098 * 165 ^ 2 + 26 / (10 * 13098)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3602649 / 1000000000))) * ((217205683 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3602649 / 1000000000)) ^ 3) * ((1326649479 / 1000000000000000000000000))) + ((3992219207 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3602649 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13098) : ℝ)) d.D d.V d.P (√(tA 13098) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3602649 / 1000000000)) ^ 2 * (((1042126871 / 500000000000000)) * ((4552899967 / 125000000000000000)))) + ((3992219207 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13098) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3602649 / 1000000000)) * ((217205683 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13098) : ℝ)) (tA 13098 * 165 ^ 2 + 26 / (10 * 13098)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((217205683 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3602649 / 1000000000)) ^ 2) * ((1326649479 / 1000000000000000000000000)) + ((3992219207 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13098) : ℝ)) (√(26 / (10 * 13098) : ℝ)) d.D d.V d.P (√(tA 13098) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3602649 / 1000000000)) * (((1042126871 / 500000000000000)) * ((4552899967 / 125000000000000000))) + ((3992219207 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13098) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((217205683 / 50000000000000000000) : ℝ) + ((3992219207 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13098

namespace BstLean.Part266.Row13098
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13098 165 ∧
    0 ≤ (tableEnvelope C).f1 13098 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13098 165 ∧
    0 ≤ (tableEnvelope C).w1 13098 165 ∧ 0 ≤ (tableEnvelope C).w2 13098 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13098 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13098 165 ∧ 0 ≤ d.f1 13098 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13098 165 ∧ 0 ≤ d.w1 13098 165 ∧ 0 ≤ d.w2 13098 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13098 ≤ 2 * (228 / 100 : ℝ) / 13098 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13098 ≤ 2 * (370 / 100 : ℝ) / 13098 := by
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
    (completeRAData (tableEnvelope C) 13098 165).locationBound 13098 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13098 165).energyBound 13098 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13098 165) (d.f1 13098 165) d.f2 ≤
      32 * (((424244559 / 100000000000000000) : ℝ) + (1415351741 / 1000000000000000000) + (170090183 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13098 165) (d.w1 13098 165)
      (d.w2 13098 165) ≤
      32 * (((1671104867 / 100000000000000000000) : ℝ) + (594479623 / 50000000000000000000) + (217207617 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13098 165) (d.f1 13098 165) d.f2 ≤
      ((424244559 / 100000000000000000) : ℝ) ^ 2 + 2 * ((424244559 / 100000000000000000)) * ((1415351741 / 1000000000000000000)) * (126 / 100) +
      2 * (((1415351741 / 1000000000000000000)) ^ 2 + 2 * ((424244559 / 100000000000000000)) * ((170090183 / 500000000000000000))) +
      6 * ((1415351741 / 1000000000000000000)) * ((170090183 / 500000000000000000)) * (126 / 100) + 8 * ((170090183 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13098 165) (d.f1 13098 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13098 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13098 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13098 165) (d.f1 13098 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13098 165) (d.w1 13098 165) (d.w2 13098 165)
  have hwexpr0 : 0 ≤ d.w0 13098 165 + d.w1 13098 165 * √(π / 2) +
      2 * d.w2 13098 165 + energyR16 13098 *
      radiusPolynomialRoot16 (d.w0 13098 165) (d.w1 13098 165) (d.w2 13098 165) := by
    positivity
  constructor
  · change (13098 : ℝ) ^ 8 * (mA 13098 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13098 165) (d.f1 13098 165) d.f2 + locationR16 13098 *
        radiusPolynomialRoot16 (d.f0 13098 165) (d.f1 13098 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13098 : ℝ) ^ 8 * (mA 13098 : ℝ) ^ 8 *
        ((((424244559 / 100000000000000000) : ℝ) ^ 2 + 2 * ((424244559 / 100000000000000000)) * ((1415351741 / 1000000000000000000)) * (126 / 100) +
          2 * (((1415351741 / 1000000000000000000)) ^ 2 + 2 * ((424244559 / 100000000000000000)) * ((170090183 / 500000000000000000))) +
          6 * ((1415351741 / 1000000000000000000)) * ((170090183 / 500000000000000000)) * (126 / 100) + 8 * ((170090183 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13098) *
          (32 * (((424244559 / 100000000000000000) : ℝ) + (1415351741 / 1000000000000000000) + (170090183 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13098 : ℝ) ^ 16 *
      (d.w0 13098 165 + d.w1 13098 165 * √(π / 2) + 2 * d.w2 13098 165 +
        energyR16 13098 * radiusPolynomialRoot16 (d.w0 13098 165) (d.w1 13098 165)
          (d.w2 13098 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13098 : ℝ) ^ 16 *
        (((1671104867 / 100000000000000000000) : ℝ) + ((594479623 / 50000000000000000000)) * (126 / 100) + 2 * ((217207617 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13098) *
          (32 * (((1671104867 / 100000000000000000000) : ℝ) + (594479623 / 50000000000000000000) + (217207617 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13098

/-! A coarse bound on the actual paper statistics constant at dimension 13099. -/
namespace BstLean.Part266.Row13099
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_radius_constant : exactRadius 13097 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13097 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13097 128 ≤ (13351 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13351 : ℝ) := by
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

theorem table_statistics_constant : statisticsConstant (paperBound256 13099) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13099 : ℕ))
    (by norm_num : (13099 : ℕ) ≤ 16384)
  have ht : paperTail256 13099 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13099 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13099 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13099 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13099 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13099 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13097 128 * √(2 / (13099 : ℝ)) *
      (√(13099 : ℝ) + paperT0 13099 + paperTail256 13099) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13099 ≤ 1002 / 1000 := by
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
  have hL0 : 0 ≤ paperLJ256 13099 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13099 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13097 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13097 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13099 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13099

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13099
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13099 (61 / 100) 165 (17 / (100 * 13099)) (26 / (10 * 13099)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13099 (61 / 100) 165 (17 / (100 * 13099)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (434311877 / 100000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (265248879 / 200000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3989758811 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13099 / 13099 * (61 / 100)) ^ 4 * inverseRadius8 (13099 - 1) /
            envelopeGap 13099 (61 / 100) 165 (17 / (100 * 13099)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13099

namespace BstLean.Part266.Row13099
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13099 165 ≤ (1060409383 / 250000000000000000)
  f1 : (tableEnvelope C).f1 13099 165 ≤ (1415081991 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (170057743 / 500000000000000000)
  w0 : (tableEnvelope C).w0 13099 165 ≤ (1670722481 / 100000000000000000000)
  w1 : (tableEnvelope C).w1 13099 165 ≤ (118868711 / 10000000000000000000)
  w2 : (tableEnvelope C).w2 13099 165 ≤ (217157871 / 50000000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (434311877 / 100000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (434311877 / 100000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (265248879 / 200000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3989758811 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((3602511 / 1000000000) : ℝ) ≤ √(17 / (100 * 13099) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13099) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (104200753 / 50000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7283527703 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13099) * 165 ≤ 186 / 10000 := by
    have hs : √(tA 13099) ≤ (26990869 / 250000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13099) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13099 * (165 : ℝ) ^ 2 + 26 / (10 * 13099) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13099) : ℝ)) (tA 13099 * 165 ^ 2 + 26 / (10 * 13099)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((3602511 / 1000000000))) * ((434311877 / 100000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((3602511 / 1000000000)) ^ 3) * ((265248879 / 200000000000000000000000))) + ((3989758811 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((3602511 / 1000000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF1 (√(17 / (100 * 13099) : ℝ)) d.D d.V d.P (√(tA 13099) * 165) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((3602511 / 1000000000)) ^ 2 * (((104200753 / 50000000000000)) * ((7283527703 / 200000000000000000)))) + ((3989758811 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AF2 (√(17 / (100 * 13099) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((3602511 / 1000000000)) * ((434311877 / 100000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW0 (√(17 / (100 * 13099) : ℝ)) (tA 13099 * 165 ^ 2 + 26 / (10 * 13099)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((434311877 / 100000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((3602511 / 1000000000)) ^ 2) * ((265248879 / 200000000000000000000000)) + ((3989758811 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW1 (√(17 / (100 * 13099) : ℝ)) (√(26 / (10 * 13099) : ℝ)) d.D d.V d.P (√(tA 13099) * 165) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((3602511 / 1000000000)) * (((104200753 / 50000000000000)) * ((7283527703 / 200000000000000000))) + ((3989758811 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
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
    change AW2 d.D d.P (√(tA 13099) * 165) ≤ _
    unfold AW2
    calc
      _ ≤ ((434311877 / 100000000000000000000) : ℝ) + ((3989758811 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13099

namespace BstLean.Part266.Row13099
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13099 165 ∧
    0 ≤ (tableEnvelope C).f1 13099 165 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13099 165 ∧
    0 ≤ (tableEnvelope C).w1 13099 165 ∧ 0 ≤ (tableEnvelope C).w2 13099 165 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13099 * (165 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13099 165 ∧ 0 ≤ d.f1 13099 165 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13099 165 ∧ 0 ≤ d.w1 13099 165 ∧ 0 ≤ d.w2 13099 165
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13099 ≤ 2 * (228 / 100 : ℝ) / 13099 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13099 ≤ 2 * (370 / 100 : ℝ) / 13099 := by
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
    (completeRAData (tableEnvelope C) 13099 165).locationBound 13099 165 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13099 165).energyBound 13099 165 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13099 165) (d.f1 13099 165) d.f2 ≤
      32 * (((1060409383 / 250000000000000000) : ℝ) + (1415081991 / 1000000000000000000) + (170057743 / 500000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13099 165) (d.w1 13099 165)
      (d.w2 13099 165) ≤
      32 * (((1670722481 / 100000000000000000000) : ℝ) + (118868711 / 10000000000000000000) + (217157871 / 50000000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13099 165) (d.f1 13099 165) d.f2 ≤
      ((1060409383 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1060409383 / 250000000000000000)) * ((1415081991 / 1000000000000000000)) * (126 / 100) +
      2 * (((1415081991 / 1000000000000000000)) ^ 2 + 2 * ((1060409383 / 250000000000000000)) * ((170057743 / 500000000000000000))) +
      6 * ((1415081991 / 1000000000000000000)) * ((170057743 / 500000000000000000)) * (126 / 100) + 8 * ((170057743 / 500000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13099 165) (d.f1 13099 165) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13099 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13099 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13099 165) (d.f1 13099 165) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13099 165) (d.w1 13099 165) (d.w2 13099 165)
  have hwexpr0 : 0 ≤ d.w0 13099 165 + d.w1 13099 165 * √(π / 2) +
      2 * d.w2 13099 165 + energyR16 13099 *
      radiusPolynomialRoot16 (d.w0 13099 165) (d.w1 13099 165) (d.w2 13099 165) := by
    positivity
  constructor
  · change (13099 : ℝ) ^ 8 * (mA 13099 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13099 165) (d.f1 13099 165) d.f2 + locationR16 13099 *
        radiusPolynomialRoot16 (d.f0 13099 165) (d.f1 13099 165) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13099 : ℝ) ^ 8 * (mA 13099 : ℝ) ^ 8 *
        ((((1060409383 / 250000000000000000) : ℝ) ^ 2 + 2 * ((1060409383 / 250000000000000000)) * ((1415081991 / 1000000000000000000)) * (126 / 100) +
          2 * (((1415081991 / 1000000000000000000)) ^ 2 + 2 * ((1060409383 / 250000000000000000)) * ((170057743 / 500000000000000000))) +
          6 * ((1415081991 / 1000000000000000000)) * ((170057743 / 500000000000000000)) * (126 / 100) + 8 * ((170057743 / 500000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13099) *
          (32 * (((1060409383 / 250000000000000000) : ℝ) + (1415081991 / 1000000000000000000) + (170057743 / 500000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13099 : ℝ) ^ 16 *
      (d.w0 13099 165 + d.w1 13099 165 * √(π / 2) + 2 * d.w2 13099 165 +
        energyR16 13099 * radiusPolynomialRoot16 (d.w0 13099 165) (d.w1 13099 165)
          (d.w2 13099 165)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13099 : ℝ) ^ 16 *
        (((1670722481 / 100000000000000000000) : ℝ) + ((118868711 / 10000000000000000000)) * (126 / 100) + 2 * ((217157871 / 50000000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13099) *
          (32 * (((1670722481 / 100000000000000000000) : ℝ) + (118868711 / 10000000000000000000) + (217157871 / 50000000000000000000)))) ^ 16 := by
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

end BstLean.Part266.Row13099
